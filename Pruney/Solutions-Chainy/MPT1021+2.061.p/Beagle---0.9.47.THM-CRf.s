%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:09 EST 2020

% Result     : Theorem 9.46s
% Output     : CNFRefutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :  576 (19323 expanded)
%              Number of leaves         :   47 (6815 expanded)
%              Depth                    :   30
%              Number of atoms          : 1316 (55292 expanded)
%              Number of equality atoms :  212 (4551 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_147,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_157,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_121,axiom,(
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

tff(f_135,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_10676,plain,(
    ! [B_538,A_539] :
      ( v1_relat_1(B_538)
      | ~ m1_subset_1(B_538,k1_zfmisc_1(A_539))
      | ~ v1_relat_1(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10682,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_10676])).

tff(c_10688,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10682])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_11071,plain,(
    ! [C_588,A_589,B_590] :
      ( v2_funct_1(C_588)
      | ~ v3_funct_2(C_588,A_589,B_590)
      | ~ v1_funct_1(C_588)
      | ~ m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11083,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_11071])).

tff(c_11091,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_11083])).

tff(c_50,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10776,plain,(
    ! [A_557,B_558,D_559] :
      ( r2_relset_1(A_557,B_558,D_559,D_559)
      | ~ m1_subset_1(D_559,k1_zfmisc_1(k2_zfmisc_1(A_557,B_558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10781,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_50,c_10776])).

tff(c_10758,plain,(
    ! [C_551,B_552,A_553] :
      ( v5_relat_1(C_551,B_552)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(A_553,B_552))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10766,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_10758])).

tff(c_10784,plain,(
    ! [B_561,A_562] :
      ( k2_relat_1(B_561) = A_562
      | ~ v2_funct_2(B_561,A_562)
      | ~ v5_relat_1(B_561,A_562)
      | ~ v1_relat_1(B_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10790,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10766,c_10784])).

tff(c_10796,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_10790])).

tff(c_10818,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_10796])).

tff(c_10887,plain,(
    ! [C_576,B_577,A_578] :
      ( v2_funct_2(C_576,B_577)
      | ~ v3_funct_2(C_576,A_578,B_577)
      | ~ v1_funct_1(C_576)
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(A_578,B_577))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10896,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_10887])).

tff(c_10901,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_10896])).

tff(c_10903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10818,c_10901])).

tff(c_10904,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10796])).

tff(c_56,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_18,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_74,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_partfun1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_40] :
      ( m1_subset_1(A_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_10910,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10904,c_58])).

tff(c_10920,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_72,c_10910])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10954,plain,(
    v4_relat_1('#skF_2',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10920,c_24])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10960,plain,
    ( k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10954,c_14])).

tff(c_10963,plain,(
    k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_10960])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10967,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10963,c_12])).

tff(c_10971,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_10904,c_10967])).

tff(c_11124,plain,(
    ! [A_596,B_597] :
      ( k9_relat_1(k2_funct_1(A_596),k9_relat_1(A_596,B_597)) = B_597
      | ~ r1_tarski(B_597,k1_relat_1(A_596))
      | ~ v2_funct_1(A_596)
      | ~ v1_funct_1(A_596)
      | ~ v1_relat_1(A_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11142,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10971,c_11124])).

tff(c_11154,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_72,c_11091,c_6,c_11142])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( k9_relat_1(k2_funct_1(A_12),k9_relat_1(A_12,B_14)) = B_14
      | ~ r1_tarski(B_14,k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11162,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11154,c_16])).

tff(c_11168,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_11162])).

tff(c_11370,plain,(
    ! [A_614,B_615] :
      ( k2_funct_2(A_614,B_615) = k2_funct_1(B_615)
      | ~ m1_subset_1(B_615,k1_zfmisc_1(k2_zfmisc_1(A_614,A_614)))
      | ~ v3_funct_2(B_615,A_614,A_614)
      | ~ v1_funct_2(B_615,A_614,A_614)
      | ~ v1_funct_1(B_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_11376,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_11370])).

tff(c_11380,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11376])).

tff(c_11589,plain,(
    ! [A_632,B_633] :
      ( m1_subset_1(k2_funct_2(A_632,B_633),k1_zfmisc_1(k2_zfmisc_1(A_632,A_632)))
      | ~ m1_subset_1(B_633,k1_zfmisc_1(k2_zfmisc_1(A_632,A_632)))
      | ~ v3_funct_2(B_633,A_632,A_632)
      | ~ v1_funct_2(B_633,A_632,A_632)
      | ~ v1_funct_1(B_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_11619,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11380,c_11589])).

tff(c_11633,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_11619])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11660,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_11633,c_8])).

tff(c_11684,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11660])).

tff(c_11686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11168,c_11684])).

tff(c_11688,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_11162])).

tff(c_12601,plain,(
    ! [A_691,B_692] :
      ( k2_funct_2(A_691,B_692) = k2_funct_1(B_692)
      | ~ m1_subset_1(B_692,k1_zfmisc_1(k2_zfmisc_1(A_691,A_691)))
      | ~ v3_funct_2(B_692,A_691,A_691)
      | ~ v1_funct_2(B_692,A_691,A_691)
      | ~ v1_funct_1(B_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12607,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_12601])).

tff(c_12611,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_12607])).

tff(c_12276,plain,(
    ! [A_670,B_671] :
      ( v1_funct_1(k2_funct_2(A_670,B_671))
      | ~ m1_subset_1(B_671,k1_zfmisc_1(k2_zfmisc_1(A_670,A_670)))
      | ~ v3_funct_2(B_671,A_670,A_670)
      | ~ v1_funct_2(B_671,A_670,A_670)
      | ~ v1_funct_1(B_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12282,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_12276])).

tff(c_12286,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_12282])).

tff(c_12612,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12611,c_12286])).

tff(c_12637,plain,(
    ! [A_693,B_694] :
      ( v3_funct_2(k2_funct_2(A_693,B_694),A_693,A_693)
      | ~ m1_subset_1(B_694,k1_zfmisc_1(k2_zfmisc_1(A_693,A_693)))
      | ~ v3_funct_2(B_694,A_693,A_693)
      | ~ v1_funct_2(B_694,A_693,A_693)
      | ~ v1_funct_1(B_694) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12641,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_12637])).

tff(c_12645,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_12611,c_12641])).

tff(c_12819,plain,(
    ! [A_697,B_698] :
      ( m1_subset_1(k2_funct_2(A_697,B_698),k1_zfmisc_1(k2_zfmisc_1(A_697,A_697)))
      | ~ m1_subset_1(B_698,k1_zfmisc_1(k2_zfmisc_1(A_697,A_697)))
      | ~ v3_funct_2(B_698,A_697,A_697)
      | ~ v1_funct_2(B_698,A_697,A_697)
      | ~ v1_funct_1(B_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12849,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12611,c_12819])).

tff(c_12863,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_12849])).

tff(c_30,plain,(
    ! [C_25,B_24,A_23] :
      ( v2_funct_2(C_25,B_24)
      | ~ v3_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_12876,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12863,c_30])).

tff(c_12905,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12612,c_12645,c_12876])).

tff(c_22,plain,(
    ! [C_18,B_17,A_16] :
      ( v5_relat_1(C_18,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12910,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12863,c_22])).

tff(c_38,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(B_27) = A_26
      | ~ v2_funct_2(B_27,A_26)
      | ~ v5_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12917,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12910,c_38])).

tff(c_12920,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_12905,c_12917])).

tff(c_12911,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12863,c_24])).

tff(c_12923,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12911,c_14])).

tff(c_12926,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_12923])).

tff(c_11897,plain,(
    ! [A_651,B_652] :
      ( k2_funct_2(A_651,B_652) = k2_funct_1(B_652)
      | ~ m1_subset_1(B_652,k1_zfmisc_1(k2_zfmisc_1(A_651,A_651)))
      | ~ v3_funct_2(B_652,A_651,A_651)
      | ~ v1_funct_2(B_652,A_651,A_651)
      | ~ v1_funct_1(B_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_11903,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_11897])).

tff(c_11907,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11903])).

tff(c_12118,plain,(
    ! [A_668,B_669] :
      ( m1_subset_1(k2_funct_2(A_668,B_669),k1_zfmisc_1(k2_zfmisc_1(A_668,A_668)))
      | ~ m1_subset_1(B_669,k1_zfmisc_1(k2_zfmisc_1(A_668,A_668)))
      | ~ v3_funct_2(B_669,A_668,A_668)
      | ~ v1_funct_2(B_669,A_668,A_668)
      | ~ v1_funct_1(B_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12148,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11907,c_12118])).

tff(c_12162,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_12148])).

tff(c_12210,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12162,c_24])).

tff(c_12222,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12210,c_14])).

tff(c_12225,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_12222])).

tff(c_10797,plain,(
    ! [A_563] :
      ( m1_subset_1(A_563,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_563),k2_relat_1(A_563))))
      | ~ v1_funct_1(A_563)
      | ~ v1_relat_1(A_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_10982,plain,(
    ! [A_581] :
      ( v5_relat_1(A_581,k2_relat_1(A_581))
      | ~ v1_funct_1(A_581)
      | ~ v1_relat_1(A_581) ) ),
    inference(resolution,[status(thm)],[c_10797,c_22])).

tff(c_11710,plain,(
    ! [B_636,A_637] :
      ( v5_relat_1(k7_relat_1(B_636,A_637),k9_relat_1(B_636,A_637))
      | ~ v1_funct_1(k7_relat_1(B_636,A_637))
      | ~ v1_relat_1(k7_relat_1(B_636,A_637))
      | ~ v1_relat_1(B_636) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10982])).

tff(c_11719,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11154,c_11710])).

tff(c_11749,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_11719])).

tff(c_11854,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_11749])).

tff(c_12270,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12225,c_11854])).

tff(c_12273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_12270])).

tff(c_12275,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_11749])).

tff(c_12321,plain,(
    ! [A_675,B_676] :
      ( k2_funct_2(A_675,B_676) = k2_funct_1(B_676)
      | ~ m1_subset_1(B_676,k1_zfmisc_1(k2_zfmisc_1(A_675,A_675)))
      | ~ v3_funct_2(B_676,A_675,A_675)
      | ~ v1_funct_2(B_676,A_675,A_675)
      | ~ v1_funct_1(B_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12327,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_12321])).

tff(c_12331,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_12327])).

tff(c_12332,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12331,c_12286])).

tff(c_12486,plain,(
    ! [A_689,B_690] :
      ( m1_subset_1(k2_funct_2(A_689,B_690),k1_zfmisc_1(k2_zfmisc_1(A_689,A_689)))
      | ~ m1_subset_1(B_690,k1_zfmisc_1(k2_zfmisc_1(A_689,A_689)))
      | ~ v3_funct_2(B_690,A_689,A_689)
      | ~ v1_funct_2(B_690,A_689,A_689)
      | ~ v1_funct_1(B_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12516,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12331,c_12486])).

tff(c_12530,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_12516])).

tff(c_12578,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12530,c_24])).

tff(c_12590,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12578,c_14])).

tff(c_12593,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_12590])).

tff(c_12274,plain,
    ( ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_11749])).

tff(c_12287,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_12274])).

tff(c_12594,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12593,c_12287])).

tff(c_12598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12332,c_12594])).

tff(c_12599,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12274])).

tff(c_12622,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2')
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_12599,c_38])).

tff(c_12625,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2')
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12275,c_12622])).

tff(c_12631,plain,(
    ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12625])).

tff(c_12600,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_12274])).

tff(c_36,plain,(
    ! [B_27] :
      ( v2_funct_2(B_27,k2_relat_1(B_27))
      | ~ v5_relat_1(B_27,k2_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11001,plain,(
    ! [A_583] :
      ( v2_funct_2(A_583,k2_relat_1(A_583))
      | ~ v1_funct_1(A_583)
      | ~ v1_relat_1(A_583) ) ),
    inference(resolution,[status(thm)],[c_10982,c_36])).

tff(c_11806,plain,(
    ! [B_644,A_645] :
      ( v2_funct_2(k7_relat_1(B_644,A_645),k9_relat_1(B_644,A_645))
      | ~ v1_funct_1(k7_relat_1(B_644,A_645))
      | ~ v1_relat_1(k7_relat_1(B_644,A_645))
      | ~ v1_relat_1(B_644) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_11001])).

tff(c_11812,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11154,c_11806])).

tff(c_11841,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11688,c_11812])).

tff(c_12633,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12275,c_12600,c_11841])).

tff(c_12634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12631,c_12633])).

tff(c_12635,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_12625])).

tff(c_12978,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12926,c_12635])).

tff(c_12982,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12920,c_12978])).

tff(c_10699,plain,(
    ! [C_543,A_544,B_545] :
      ( v4_relat_1(C_543,A_544)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10707,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_10699])).

tff(c_10709,plain,(
    ! [B_547,A_548] :
      ( k7_relat_1(B_547,A_548) = B_547
      | ~ v4_relat_1(B_547,A_548)
      | ~ v1_relat_1(B_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10715,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10707,c_10709])).

tff(c_10721,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_10715])).

tff(c_10725,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10721,c_12])).

tff(c_10729,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_10725])).

tff(c_10906,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10904,c_10729])).

tff(c_11145,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10906,c_11124])).

tff(c_11156,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_72,c_11091,c_11145])).

tff(c_11166,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11154,c_11156])).

tff(c_11167,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_11166])).

tff(c_13004,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12982,c_11167])).

tff(c_13014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13004])).

tff(c_13015,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11166])).

tff(c_13193,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13015,c_11162])).

tff(c_13194,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_13193])).

tff(c_13261,plain,(
    ! [A_716,B_717] :
      ( k2_funct_2(A_716,B_717) = k2_funct_1(B_717)
      | ~ m1_subset_1(B_717,k1_zfmisc_1(k2_zfmisc_1(A_716,A_716)))
      | ~ v3_funct_2(B_717,A_716,A_716)
      | ~ v1_funct_2(B_717,A_716,A_716)
      | ~ v1_funct_1(B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_13267,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_13261])).

tff(c_13271,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_13267])).

tff(c_13402,plain,(
    ! [A_731,B_732] :
      ( m1_subset_1(k2_funct_2(A_731,B_732),k1_zfmisc_1(k2_zfmisc_1(A_731,A_731)))
      | ~ m1_subset_1(B_732,k1_zfmisc_1(k2_zfmisc_1(A_731,A_731)))
      | ~ v3_funct_2(B_732,A_731,A_731)
      | ~ v1_funct_2(B_732,A_731,A_731)
      | ~ v1_funct_1(B_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_13432,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13271,c_13402])).

tff(c_13446,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_13432])).

tff(c_13473,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_13446,c_8])).

tff(c_13497,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_13473])).

tff(c_13499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13194,c_13497])).

tff(c_13501,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_13193])).

tff(c_13045,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13015,c_11154])).

tff(c_13101,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13045,c_16])).

tff(c_14178,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13501,c_13101])).

tff(c_14179,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14178])).

tff(c_14242,plain,(
    ! [A_779,B_780] :
      ( k2_funct_2(A_779,B_780) = k2_funct_1(B_780)
      | ~ m1_subset_1(B_780,k1_zfmisc_1(k2_zfmisc_1(A_779,A_779)))
      | ~ v3_funct_2(B_780,A_779,A_779)
      | ~ v1_funct_2(B_780,A_779,A_779)
      | ~ v1_funct_1(B_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14248,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_14242])).

tff(c_14252,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_14248])).

tff(c_13181,plain,(
    ! [A_708,B_709] :
      ( v1_funct_1(k2_funct_2(A_708,B_709))
      | ~ m1_subset_1(B_709,k1_zfmisc_1(k2_zfmisc_1(A_708,A_708)))
      | ~ v3_funct_2(B_709,A_708,A_708)
      | ~ v1_funct_2(B_709,A_708,A_708)
      | ~ v1_funct_1(B_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_13187,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_13181])).

tff(c_13191,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_13187])).

tff(c_14253,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14252,c_13191])).

tff(c_14258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14179,c_14253])).

tff(c_14260,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14178])).

tff(c_14326,plain,(
    ! [A_781,B_782] :
      ( k2_funct_2(A_781,B_782) = k2_funct_1(B_782)
      | ~ m1_subset_1(B_782,k1_zfmisc_1(k2_zfmisc_1(A_781,A_781)))
      | ~ v3_funct_2(B_782,A_781,A_781)
      | ~ v1_funct_2(B_782,A_781,A_781)
      | ~ v1_funct_1(B_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14332,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_14326])).

tff(c_14336,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_14332])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_funct_2(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14837,plain,(
    ! [D_794,A_797,E_796,B_795,C_799,F_798] :
      ( k1_partfun1(A_797,B_795,C_799,D_794,E_796,F_798) = k5_relat_1(E_796,F_798)
      | ~ m1_subset_1(F_798,k1_zfmisc_1(k2_zfmisc_1(C_799,D_794)))
      | ~ v1_funct_1(F_798)
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(A_797,B_795)))
      | ~ v1_funct_1(E_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_14847,plain,(
    ! [A_797,B_795,E_796] :
      ( k1_partfun1(A_797,B_795,'#skF_1','#skF_1',E_796,'#skF_2') = k5_relat_1(E_796,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(A_797,B_795)))
      | ~ v1_funct_1(E_796) ) ),
    inference(resolution,[status(thm)],[c_66,c_14837])).

tff(c_14879,plain,(
    ! [A_800,B_801,E_802] :
      ( k1_partfun1(A_800,B_801,'#skF_1','#skF_1',E_802,'#skF_2') = k5_relat_1(E_802,'#skF_2')
      | ~ m1_subset_1(E_802,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801)))
      | ~ v1_funct_1(E_802) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14847])).

tff(c_15263,plain,(
    ! [A_810,B_811] :
      ( k1_partfun1(A_810,A_810,'#skF_1','#skF_1',k2_funct_2(A_810,B_811),'#skF_2') = k5_relat_1(k2_funct_2(A_810,B_811),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_810,B_811))
      | ~ m1_subset_1(B_811,k1_zfmisc_1(k2_zfmisc_1(A_810,A_810)))
      | ~ v3_funct_2(B_811,A_810,A_810)
      | ~ v1_funct_2(B_811,A_810,A_810)
      | ~ v1_funct_1(B_811) ) ),
    inference(resolution,[status(thm)],[c_40,c_14879])).

tff(c_15273,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_15263])).

tff(c_15284,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_14260,c_14336,c_14336,c_14336,c_15273])).

tff(c_97,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_97])).

tff(c_109,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_503,plain,(
    ! [C_100,A_101,B_102] :
      ( v2_funct_1(C_100)
      | ~ v3_funct_2(C_100,A_101,B_102)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_515,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_503])).

tff(c_523,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_515])).

tff(c_197,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_202,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_50,c_197])).

tff(c_111,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_119,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_111])).

tff(c_205,plain,(
    ! [B_72,A_73] :
      ( k2_relat_1(B_72) = A_73
      | ~ v2_funct_2(B_72,A_73)
      | ~ v5_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_211,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_119,c_205])).

tff(c_217,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_211])).

tff(c_218,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_326,plain,(
    ! [C_89,B_90,A_91] :
      ( v2_funct_2(C_89,B_90)
      | ~ v3_funct_2(C_89,A_91,B_90)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_335,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_326])).

tff(c_340,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_335])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_340])).

tff(c_343,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_365,plain,(
    ! [A_92] :
      ( m1_subset_1(A_92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_92),k2_relat_1(A_92))))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_379,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_365])).

tff(c_390,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_379])).

tff(c_403,plain,(
    v4_relat_1('#skF_2',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_390,c_24])).

tff(c_411,plain,
    ( k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_403,c_14])).

tff(c_414,plain,(
    k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_411])).

tff(c_418,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_12])).

tff(c_422,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_343,c_418])).

tff(c_585,plain,(
    ! [A_111,B_112] :
      ( k9_relat_1(k2_funct_1(A_111),k9_relat_1(A_111,B_112)) = B_112
      | ~ r1_tarski(B_112,k1_relat_1(A_111))
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_603,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_585])).

tff(c_615,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_523,c_6,c_603])).

tff(c_428,plain,(
    ! [A_93] :
      ( v5_relat_1(A_93,k2_relat_1(A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_365,c_22])).

tff(c_648,plain,(
    ! [B_114,A_115] :
      ( v5_relat_1(k7_relat_1(B_114,A_115),k9_relat_1(B_114,A_115))
      | ~ v1_funct_1(k7_relat_1(B_114,A_115))
      | ~ v1_relat_1(k7_relat_1(B_114,A_115))
      | ~ v1_relat_1(B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_428])).

tff(c_657,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_648])).

tff(c_782,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_823,plain,(
    ! [A_128,B_129] :
      ( k2_funct_2(A_128,B_129) = k2_funct_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v3_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_829,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_823])).

tff(c_833,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_829])).

tff(c_982,plain,(
    ! [A_143,B_144] :
      ( m1_subset_1(k2_funct_2(A_143,B_144),k1_zfmisc_1(k2_zfmisc_1(A_143,A_143)))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(A_143,A_143)))
      | ~ v3_funct_2(B_144,A_143,A_143)
      | ~ v1_funct_2(B_144,A_143,A_143)
      | ~ v1_funct_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1012,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_982])).

tff(c_1026,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_1012])).

tff(c_1053,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1026,c_8])).

tff(c_1077,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1053])).

tff(c_1079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_1077])).

tff(c_1081,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_624,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_16])).

tff(c_1701,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_624])).

tff(c_1702,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1701])).

tff(c_1746,plain,(
    ! [A_186,B_187] :
      ( k2_funct_2(A_186,B_187) = k2_funct_1(B_187)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1752,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1746])).

tff(c_1756,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1752])).

tff(c_1734,plain,(
    ! [A_183,B_184] :
      ( v1_funct_1(k2_funct_2(A_183,B_184))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1740,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1734])).

tff(c_1744,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1740])).

tff(c_1757,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_1744])).

tff(c_1760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1702,c_1757])).

tff(c_1762,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1701])).

tff(c_2173,plain,(
    ! [A_209,B_210] :
      ( k2_funct_2(A_209,B_210) = k2_funct_1(B_210)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v3_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2179,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2173])).

tff(c_2183,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2179])).

tff(c_2230,plain,(
    ! [A_211,B_212] :
      ( v3_funct_2(k2_funct_2(A_211,B_212),A_211,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k2_zfmisc_1(A_211,A_211)))
      | ~ v3_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2234,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2230])).

tff(c_2238,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2183,c_2234])).

tff(c_3122,plain,(
    ! [A_259,B_260] :
      ( m1_subset_1(k2_funct_2(A_259,B_260),k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3152,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2183,c_3122])).

tff(c_3166,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_3152])).

tff(c_3179,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3166,c_30])).

tff(c_3208,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_2238,c_3179])).

tff(c_3213,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3166,c_24])).

tff(c_3220,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3213,c_14])).

tff(c_3223,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_3220])).

tff(c_1126,plain,(
    ! [A_150,B_151] :
      ( k2_funct_2(A_150,B_151) = k2_funct_1(B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_zfmisc_1(A_150,A_150)))
      | ~ v3_funct_2(B_151,A_150,A_150)
      | ~ v1_funct_2(B_151,A_150,A_150)
      | ~ v1_funct_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1132,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1126])).

tff(c_1136,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1132])).

tff(c_1517,plain,(
    ! [A_174,B_175] :
      ( m1_subset_1(k2_funct_2(A_174,B_175),k1_zfmisc_1(k2_zfmisc_1(A_174,A_174)))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k2_zfmisc_1(A_174,A_174)))
      | ~ v3_funct_2(B_175,A_174,A_174)
      | ~ v1_funct_2(B_175,A_174,A_174)
      | ~ v1_funct_1(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1547,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_1517])).

tff(c_1561,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_1547])).

tff(c_1608,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1561,c_24])).

tff(c_1615,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1608,c_14])).

tff(c_1618,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1615])).

tff(c_461,plain,(
    ! [A_97] :
      ( v2_funct_2(A_97,k2_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_428,c_36])).

tff(c_736,plain,(
    ! [B_122,A_123] :
      ( v2_funct_2(k7_relat_1(B_122,A_123),k9_relat_1(B_122,A_123))
      | ~ v1_funct_1(k7_relat_1(B_122,A_123))
      | ~ v1_relat_1(k7_relat_1(B_122,A_123))
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_461])).

tff(c_742,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_736])).

tff(c_1083,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_742])).

tff(c_1084,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1083])).

tff(c_1694,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1084])).

tff(c_1697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1694])).

tff(c_1699,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1083])).

tff(c_1778,plain,(
    ! [A_190,B_191] :
      ( k2_funct_2(A_190,B_191) = k2_funct_1(B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1784,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1778])).

tff(c_1788,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1784])).

tff(c_1917,plain,(
    ! [A_205,B_206] :
      ( m1_subset_1(k2_funct_2(A_205,B_206),k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1947,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_1917])).

tff(c_1961,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_1947])).

tff(c_2008,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1961,c_24])).

tff(c_2015,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2008,c_14])).

tff(c_2018,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_2015])).

tff(c_1698,plain,
    ( ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1083])).

tff(c_1763,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1698])).

tff(c_2025,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_1763])).

tff(c_2029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_2025])).

tff(c_2030,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1698])).

tff(c_2031,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1698])).

tff(c_1080,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_2045,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_1699,c_1080])).

tff(c_2048,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2')
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_2045,c_38])).

tff(c_2051,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_2030,c_2048])).

tff(c_3241,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3223,c_2051])).

tff(c_3214,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3166,c_22])).

tff(c_3226,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3214,c_38])).

tff(c_3229,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_3226])).

tff(c_3449,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3208,c_3241,c_3229])).

tff(c_130,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_138,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_130])).

tff(c_140,plain,(
    ! [B_62,A_63] :
      ( k7_relat_1(B_62,A_63) = B_62
      | ~ v4_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_138,c_140])).

tff(c_152,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_146])).

tff(c_156,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_12])).

tff(c_160,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_156])).

tff(c_345,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_160])).

tff(c_606,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_585])).

tff(c_617,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_523,c_606])).

tff(c_620,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_3455,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_620])).

tff(c_3466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3455])).

tff(c_3467,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_3502,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3467,c_615])).

tff(c_20,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_73,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_partfun1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_3578,plain,(
    ! [B_277,A_278] :
      ( v5_relat_1(k7_relat_1(B_277,A_278),k9_relat_1(B_277,A_278))
      | ~ v1_funct_1(k7_relat_1(B_277,A_278))
      | ~ v1_relat_1(k7_relat_1(B_277,A_278))
      | ~ v1_relat_1(B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_428])).

tff(c_3587,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3467,c_3578])).

tff(c_3681,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3587])).

tff(c_3711,plain,(
    ! [A_288,B_289] :
      ( k2_funct_2(A_288,B_289) = k2_funct_1(B_289)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(k2_zfmisc_1(A_288,A_288)))
      | ~ v3_funct_2(B_289,A_288,A_288)
      | ~ v1_funct_2(B_289,A_288,A_288)
      | ~ v1_funct_1(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3717,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3711])).

tff(c_3721,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_3717])).

tff(c_3889,plain,(
    ! [A_305,B_306] :
      ( m1_subset_1(k2_funct_2(A_305,B_306),k1_zfmisc_1(k2_zfmisc_1(A_305,A_305)))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_zfmisc_1(A_305,A_305)))
      | ~ v3_funct_2(B_306,A_305,A_305)
      | ~ v1_funct_2(B_306,A_305,A_305)
      | ~ v1_funct_1(B_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3919,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3721,c_3889])).

tff(c_3933,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_3919])).

tff(c_3960,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3933,c_8])).

tff(c_3984,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3960])).

tff(c_3986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3681,c_3984])).

tff(c_3988,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3587])).

tff(c_5302,plain,(
    ! [A_377,B_378] :
      ( k2_funct_2(A_377,B_378) = k2_funct_1(B_378)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(k2_zfmisc_1(A_377,A_377)))
      | ~ v3_funct_2(B_378,A_377,A_377)
      | ~ v1_funct_2(B_378,A_377,A_377)
      | ~ v1_funct_1(B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5308,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5302])).

tff(c_5312,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_5308])).

tff(c_3633,plain,(
    ! [A_281,B_282] :
      ( v1_funct_1(k2_funct_2(A_281,B_282))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(k2_zfmisc_1(A_281,A_281)))
      | ~ v3_funct_2(B_282,A_281,A_281)
      | ~ v1_funct_2(B_282,A_281,A_281)
      | ~ v1_funct_1(B_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3639,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3633])).

tff(c_3643,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_3639])).

tff(c_5313,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5312,c_3643])).

tff(c_3498,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3467,c_16])).

tff(c_6011,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5313,c_3498])).

tff(c_6012,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6011])).

tff(c_5941,plain,(
    ! [A_412,B_413] :
      ( v3_funct_2(k2_funct_2(A_412,B_413),A_412,A_412)
      | ~ m1_subset_1(B_413,k1_zfmisc_1(k2_zfmisc_1(A_412,A_412)))
      | ~ v3_funct_2(B_413,A_412,A_412)
      | ~ v1_funct_2(B_413,A_412,A_412)
      | ~ v1_funct_1(B_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5945,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5941])).

tff(c_5949,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_5312,c_5945])).

tff(c_6063,plain,(
    ! [A_418,B_419] :
      ( m1_subset_1(k2_funct_2(A_418,B_419),k1_zfmisc_1(k2_zfmisc_1(A_418,A_418)))
      | ~ m1_subset_1(B_419,k1_zfmisc_1(k2_zfmisc_1(A_418,A_418)))
      | ~ v3_funct_2(B_419,A_418,A_418)
      | ~ v1_funct_2(B_419,A_418,A_418)
      | ~ v1_funct_1(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6093,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_6063])).

tff(c_6107,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_6093])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( v2_funct_1(C_25)
      | ~ v3_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6123,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6107,c_32])).

tff(c_6152,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_5949,c_6123])).

tff(c_6154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6012,c_6152])).

tff(c_6156,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6011])).

tff(c_6881,plain,(
    ! [A_441,B_442] :
      ( v1_funct_2(k2_funct_2(A_441,B_442),A_441,A_441)
      | ~ m1_subset_1(B_442,k1_zfmisc_1(k2_zfmisc_1(A_441,A_441)))
      | ~ v3_funct_2(B_442,A_441,A_441)
      | ~ v1_funct_2(B_442,A_441,A_441)
      | ~ v1_funct_1(B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6885,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_6881])).

tff(c_6889,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_5312,c_6885])).

tff(c_7332,plain,(
    ! [A_459,B_460] :
      ( m1_subset_1(k2_funct_2(A_459,B_460),k1_zfmisc_1(k2_zfmisc_1(A_459,A_459)))
      | ~ m1_subset_1(B_460,k1_zfmisc_1(k2_zfmisc_1(A_459,A_459)))
      | ~ v3_funct_2(B_460,A_459,A_459)
      | ~ v1_funct_2(B_460,A_459,A_459)
      | ~ v1_funct_1(B_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_7362,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_7332])).

tff(c_7376,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_7362])).

tff(c_54,plain,(
    ! [A_37,B_38] :
      ( k2_funct_2(A_37,B_38) = k2_funct_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(A_37,A_37)))
      | ~ v3_funct_2(B_38,A_37,A_37)
      | ~ v1_funct_2(B_38,A_37,A_37)
      | ~ v1_funct_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_7383,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7376,c_54])).

tff(c_7412,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6889,c_5949,c_7383])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( v1_funct_1(k2_funct_2(A_28,B_29))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_7386,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7376,c_46])).

tff(c_7415,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6889,c_5949,c_7386])).

tff(c_7583,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7412,c_7415])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( v3_funct_2(k2_funct_2(A_28,B_29),A_28,A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_7380,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7376,c_42])).

tff(c_7409,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6889,c_5949,c_7380])).

tff(c_7582,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7412,c_7409])).

tff(c_7587,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7412,c_40])).

tff(c_7591,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6889,c_5949,c_7376,c_7587])).

tff(c_7645,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7591,c_30])).

tff(c_7680,plain,(
    v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7583,c_7582,c_7645])).

tff(c_7423,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7376,c_24])).

tff(c_7430,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7423,c_14])).

tff(c_7433,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_7430])).

tff(c_6939,plain,(
    ! [A_445,B_446] :
      ( m1_subset_1(k2_funct_2(A_445,B_446),k1_zfmisc_1(k2_zfmisc_1(A_445,A_445)))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(k2_zfmisc_1(A_445,A_445)))
      | ~ v3_funct_2(B_446,A_445,A_445)
      | ~ v1_funct_2(B_446,A_445,A_445)
      | ~ v1_funct_1(B_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6969,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_6939])).

tff(c_6983,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_6969])).

tff(c_7030,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6983,c_24])).

tff(c_7037,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7030,c_14])).

tff(c_7040,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_7037])).

tff(c_6168,plain,(
    ! [A_420,B_421] :
      ( v1_funct_2(k2_funct_2(A_420,B_421),A_420,A_420)
      | ~ m1_subset_1(B_421,k1_zfmisc_1(k2_zfmisc_1(A_420,A_420)))
      | ~ v3_funct_2(B_421,A_420,A_420)
      | ~ v1_funct_2(B_421,A_420,A_420)
      | ~ v1_funct_1(B_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6172,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_6168])).

tff(c_6176,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_5312,c_6172])).

tff(c_6390,plain,(
    ! [A_426,B_427] :
      ( m1_subset_1(k2_funct_2(A_426,B_427),k1_zfmisc_1(k2_zfmisc_1(A_426,A_426)))
      | ~ m1_subset_1(B_427,k1_zfmisc_1(k2_zfmisc_1(A_426,A_426)))
      | ~ v3_funct_2(B_427,A_426,A_426)
      | ~ v1_funct_2(B_427,A_426,A_426)
      | ~ v1_funct_1(B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6420,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_6390])).

tff(c_6434,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_6420])).

tff(c_6441,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6434,c_54])).

tff(c_6470,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6176,c_5949,c_6441])).

tff(c_6591,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6470,c_40])).

tff(c_6595,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6176,c_5949,c_6434,c_6591])).

tff(c_6712,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_6595,c_8])).

tff(c_6742,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6712])).

tff(c_6447,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6434,c_30])).

tff(c_6476,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_5949,c_6447])).

tff(c_6482,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6434,c_22])).

tff(c_6494,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6482,c_38])).

tff(c_6497,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_6476,c_6494])).

tff(c_446,plain,(
    ! [A_94] :
      ( v4_relat_1(A_94,k1_relat_1(A_94))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_365,c_24])).

tff(c_470,plain,(
    ! [A_98] :
      ( k7_relat_1(A_98,k1_relat_1(A_98)) = A_98
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_446,c_14])).

tff(c_479,plain,(
    ! [A_98] :
      ( k9_relat_1(A_98,k1_relat_1(A_98)) = k2_relat_1(A_98)
      | ~ v1_relat_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_12])).

tff(c_600,plain,(
    ! [A_98] :
      ( k9_relat_1(k2_funct_1(A_98),k2_relat_1(A_98)) = k1_relat_1(A_98)
      | ~ r1_tarski(k1_relat_1(A_98),k1_relat_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98)
      | ~ v1_relat_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_585])).

tff(c_613,plain,(
    ! [A_98] :
      ( k9_relat_1(k2_funct_1(A_98),k2_relat_1(A_98)) = k1_relat_1(A_98)
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_600])).

tff(c_6501,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6497,c_613])).

tff(c_6526,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5313,c_6156,c_6501])).

tff(c_6444,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6434,c_46])).

tff(c_6473,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6176,c_5949,c_6444])).

tff(c_6587,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6473])).

tff(c_6438,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6434,c_42])).

tff(c_6467,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6176,c_5949,c_6438])).

tff(c_6617,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6470,c_6467])).

tff(c_6698,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6595,c_30])).

tff(c_6733,plain,(
    v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6587,c_6617,c_6698])).

tff(c_6739,plain,(
    v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6595,c_22])).

tff(c_6755,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6739,c_38])).

tff(c_6758,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_6733,c_6755])).

tff(c_6738,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6595,c_24])).

tff(c_6749,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6738,c_14])).

tff(c_6752,plain,(
    k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_6749])).

tff(c_6859,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6752,c_12])).

tff(c_6867,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_6526,c_6758,c_6859])).

tff(c_6481,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6434,c_24])).

tff(c_6488,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6481,c_14])).

tff(c_6491,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_6488])).

tff(c_5619,plain,(
    ! [A_400,B_401] :
      ( m1_subset_1(k2_funct_2(A_400,B_401),k1_zfmisc_1(k2_zfmisc_1(A_400,A_400)))
      | ~ m1_subset_1(B_401,k1_zfmisc_1(k2_zfmisc_1(A_400,A_400)))
      | ~ v3_funct_2(B_401,A_400,A_400)
      | ~ v1_funct_2(B_401,A_400,A_400)
      | ~ v1_funct_1(B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5649,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_5619])).

tff(c_5663,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_5649])).

tff(c_5710,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5663,c_24])).

tff(c_5717,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5710,c_14])).

tff(c_5720,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5717])).

tff(c_4575,plain,(
    ! [A_343,B_344] :
      ( k2_funct_2(A_343,B_344) = k2_funct_1(B_344)
      | ~ m1_subset_1(B_344,k1_zfmisc_1(k2_zfmisc_1(A_343,A_343)))
      | ~ v3_funct_2(B_344,A_343,A_343)
      | ~ v1_funct_2(B_344,A_343,A_343)
      | ~ v1_funct_1(B_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4581,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_4575])).

tff(c_4585,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_4581])).

tff(c_4586,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4585,c_3643])).

tff(c_5117,plain,(
    ! [A_375,B_376] :
      ( m1_subset_1(k2_funct_2(A_375,B_376),k1_zfmisc_1(k2_zfmisc_1(A_375,A_375)))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(k2_zfmisc_1(A_375,A_375)))
      | ~ v3_funct_2(B_376,A_375,A_375)
      | ~ v1_funct_2(B_376,A_375,A_375)
      | ~ v1_funct_1(B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5147,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4585,c_5117])).

tff(c_5161,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_5147])).

tff(c_5273,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5161,c_24])).

tff(c_5280,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_5273,c_14])).

tff(c_5283,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5280])).

tff(c_3987,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3587])).

tff(c_3989,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3987])).

tff(c_5293,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5283,c_3989])).

tff(c_5299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4586,c_5293])).

tff(c_5300,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3987])).

tff(c_5319,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5300])).

tff(c_5791,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5720,c_5319])).

tff(c_5795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5791])).

tff(c_5797,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5300])).

tff(c_5301,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3987])).

tff(c_5796,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5300])).

tff(c_5800,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_5796,c_38])).

tff(c_5803,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5797,c_5800])).

tff(c_5804,plain,(
    ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5803])).

tff(c_3644,plain,(
    ! [B_283,A_284] :
      ( v2_funct_2(k7_relat_1(B_283,A_284),k9_relat_1(B_283,A_284))
      | ~ v1_funct_1(k7_relat_1(B_283,A_284))
      | ~ v1_relat_1(k7_relat_1(B_283,A_284))
      | ~ v1_relat_1(B_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_461])).

tff(c_3650,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3467,c_3644])).

tff(c_5844,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5797,c_5301,c_3650])).

tff(c_5845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5804,c_5844])).

tff(c_5846,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5803])).

tff(c_519,plain,(
    ! [A_40] :
      ( v2_funct_1(A_40)
      | ~ v3_funct_2(A_40,k1_relat_1(A_40),k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_58,c_503])).

tff(c_5856,plain,
    ( v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v3_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_519])).

tff(c_5886,plain,
    ( v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v3_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5797,c_5301,c_5856])).

tff(c_6167,plain,(
    ~ v3_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5886])).

tff(c_6544,plain,(
    ~ v3_funct_2(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6491,c_6491,c_6167])).

tff(c_6871,plain,(
    ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_6544])).

tff(c_6878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5949,c_6871])).

tff(c_6879,plain,(
    v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5886])).

tff(c_5853,plain,
    ( k9_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1') = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5846,c_613])).

tff(c_5884,plain,
    ( k9_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1') = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5797,c_5301,c_5853])).

tff(c_6893,plain,(
    k9_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1') = k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_5884])).

tff(c_467,plain,(
    ! [B_9,A_8] :
      ( v2_funct_2(k7_relat_1(B_9,A_8),k9_relat_1(B_9,A_8))
      | ~ v1_funct_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_461])).

tff(c_6897,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1'),k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6893,c_467])).

tff(c_6907,plain,(
    ~ v1_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6897])).

tff(c_7091,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7040,c_6907])).

tff(c_6990,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6983,c_54])).

tff(c_7019,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6889,c_5949,c_6990])).

tff(c_7194,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7019,c_40])).

tff(c_7198,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_6889,c_5949,c_6983,c_7194])).

tff(c_7266,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_7198,c_8])).

tff(c_7296,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7266])).

tff(c_7298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7091,c_7296])).

tff(c_7300,plain,(
    v1_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_6897])).

tff(c_7484,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7433,c_7300])).

tff(c_7389,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7376,c_30])).

tff(c_7418,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_5949,c_7389])).

tff(c_7424,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7376,c_22])).

tff(c_7436,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7424,c_38])).

tff(c_7439,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_7418,c_7436])).

tff(c_7443,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7439,c_613])).

tff(c_7468,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5313,c_6156,c_7443])).

tff(c_7685,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7591,c_24])).

tff(c_7692,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7685,c_14])).

tff(c_7695,plain,(
    k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7484,c_7692])).

tff(c_7759,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7695,c_12])).

tff(c_7767,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7484,c_7468,c_7759])).

tff(c_7686,plain,(
    v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7591,c_22])).

tff(c_7698,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7686,c_38])).

tff(c_7701,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7484,c_7698])).

tff(c_8234,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7767,c_7701])).

tff(c_6155,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6011])).

tff(c_6157,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6155])).

tff(c_8246,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8234,c_6157])).

tff(c_8258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8246])).

tff(c_8259,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6155])).

tff(c_8296,plain,(
    ! [A_485,B_486] :
      ( m1_subset_1(k2_funct_2(A_485,B_486),k1_zfmisc_1(k2_zfmisc_1(A_485,A_485)))
      | ~ m1_subset_1(B_486,k1_zfmisc_1(k2_zfmisc_1(A_485,A_485)))
      | ~ v3_funct_2(B_486,A_485,A_485)
      | ~ v1_funct_2(B_486,A_485,A_485)
      | ~ v1_funct_1(B_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8326,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5312,c_8296])).

tff(c_8340,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_66,c_8326])).

tff(c_8353,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8340,c_30])).

tff(c_8382,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_5949,c_8353])).

tff(c_8388,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8340,c_22])).

tff(c_8400,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8388,c_38])).

tff(c_8403,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_8382,c_8400])).

tff(c_8407,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8403,c_613])).

tff(c_8432,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5313,c_6156,c_8259,c_8407])).

tff(c_8260,plain,(
    r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6155])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8272,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8260,c_2])).

tff(c_8286,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8272])).

tff(c_8448,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8432,c_8286])).

tff(c_8452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8448])).

tff(c_8453,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8272])).

tff(c_8460,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8453,c_479])).

tff(c_8482,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5313,c_3988,c_3467,c_8460])).

tff(c_8691,plain,(
    ! [C_494,D_489,A_492,F_493,E_491,B_490] :
      ( k1_partfun1(A_492,B_490,C_494,D_489,E_491,F_493) = k5_relat_1(E_491,F_493)
      | ~ m1_subset_1(F_493,k1_zfmisc_1(k2_zfmisc_1(C_494,D_489)))
      | ~ v1_funct_1(F_493)
      | ~ m1_subset_1(E_491,k1_zfmisc_1(k2_zfmisc_1(A_492,B_490)))
      | ~ v1_funct_1(E_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10180,plain,(
    ! [A_525,B_526,A_527,E_528] :
      ( k1_partfun1(A_525,B_526,k1_relat_1(A_527),k2_relat_1(A_527),E_528,A_527) = k5_relat_1(E_528,A_527)
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526)))
      | ~ v1_funct_1(E_528)
      | ~ v1_funct_1(A_527)
      | ~ v1_relat_1(A_527) ) ),
    inference(resolution,[status(thm)],[c_58,c_8691])).

tff(c_10198,plain,(
    ! [A_527] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_527),k2_relat_1(A_527),'#skF_2',A_527) = k5_relat_1('#skF_2',A_527)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_funct_1(A_527)
      | ~ v1_relat_1(A_527) ) ),
    inference(resolution,[status(thm)],[c_66,c_10180])).

tff(c_10288,plain,(
    ! [A_529] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_529),k2_relat_1(A_529),'#skF_2',A_529) = k5_relat_1('#skF_2',A_529)
      | ~ v1_funct_1(A_529)
      | ~ v1_relat_1(A_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_10198])).

tff(c_10312,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1',k2_relat_1(k2_funct_1('#skF_2')),'#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8453,c_10288])).

tff(c_10335,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3988,c_5313,c_8482,c_10312])).

tff(c_64,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_89,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_5314,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5312,c_89])).

tff(c_10656,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10335,c_5314])).

tff(c_10663,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10656])).

tff(c_10666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_72,c_523,c_202,c_3502,c_10663])).

tff(c_10667,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_14339,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14336,c_10667])).

tff(c_15368,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15284,c_14339])).

tff(c_15426,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_15368])).

tff(c_15429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_72,c_11091,c_10781,c_10904,c_15426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.46/3.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.67  
% 9.99/3.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.99/3.68  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.99/3.68  
% 9.99/3.68  %Foreground sorts:
% 9.99/3.68  
% 9.99/3.68  
% 9.99/3.68  %Background operators:
% 9.99/3.68  
% 9.99/3.68  
% 9.99/3.68  %Foreground operators:
% 9.99/3.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.99/3.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.99/3.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.99/3.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.99/3.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.99/3.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.99/3.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.99/3.68  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.99/3.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.99/3.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.99/3.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.99/3.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.99/3.68  tff('#skF_2', type, '#skF_2': $i).
% 9.99/3.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.99/3.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.99/3.68  tff('#skF_1', type, '#skF_1': $i).
% 9.99/3.68  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.99/3.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.99/3.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.99/3.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.99/3.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.99/3.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.99/3.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.99/3.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.99/3.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.99/3.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.99/3.68  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.99/3.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.99/3.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.99/3.68  
% 10.20/3.74  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.20/3.74  tff(f_170, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 10.20/3.74  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.20/3.74  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.20/3.74  tff(f_125, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.20/3.74  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.20/3.74  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.20/3.74  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.20/3.74  tff(f_147, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.20/3.74  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 10.20/3.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.20/3.74  tff(f_157, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.20/3.74  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.20/3.74  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 10.20/3.74  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 10.20/3.74  tff(f_145, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.20/3.74  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 10.20/3.74  tff(f_135, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.20/3.74  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.20/3.74  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.20/3.74  tff(c_10676, plain, (![B_538, A_539]: (v1_relat_1(B_538) | ~m1_subset_1(B_538, k1_zfmisc_1(A_539)) | ~v1_relat_1(A_539))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.20/3.74  tff(c_10682, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_10676])).
% 10.20/3.74  tff(c_10688, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10682])).
% 10.20/3.74  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.20/3.74  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.20/3.74  tff(c_11071, plain, (![C_588, A_589, B_590]: (v2_funct_1(C_588) | ~v3_funct_2(C_588, A_589, B_590) | ~v1_funct_1(C_588) | ~m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.74  tff(c_11083, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_11071])).
% 10.20/3.74  tff(c_11091, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_11083])).
% 10.20/3.74  tff(c_50, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.20/3.74  tff(c_10776, plain, (![A_557, B_558, D_559]: (r2_relset_1(A_557, B_558, D_559, D_559) | ~m1_subset_1(D_559, k1_zfmisc_1(k2_zfmisc_1(A_557, B_558))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.20/3.74  tff(c_10781, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_50, c_10776])).
% 10.20/3.74  tff(c_10758, plain, (![C_551, B_552, A_553]: (v5_relat_1(C_551, B_552) | ~m1_subset_1(C_551, k1_zfmisc_1(k2_zfmisc_1(A_553, B_552))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.74  tff(c_10766, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_10758])).
% 10.20/3.74  tff(c_10784, plain, (![B_561, A_562]: (k2_relat_1(B_561)=A_562 | ~v2_funct_2(B_561, A_562) | ~v5_relat_1(B_561, A_562) | ~v1_relat_1(B_561))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.20/3.74  tff(c_10790, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10766, c_10784])).
% 10.20/3.74  tff(c_10796, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_10790])).
% 10.20/3.74  tff(c_10818, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_10796])).
% 10.20/3.74  tff(c_10887, plain, (![C_576, B_577, A_578]: (v2_funct_2(C_576, B_577) | ~v3_funct_2(C_576, A_578, B_577) | ~v1_funct_1(C_576) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(A_578, B_577))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.74  tff(c_10896, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_10887])).
% 10.20/3.74  tff(c_10901, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_10896])).
% 10.20/3.74  tff(c_10903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10818, c_10901])).
% 10.20/3.74  tff(c_10904, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_10796])).
% 10.20/3.74  tff(c_56, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.20/3.74  tff(c_18, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.20/3.74  tff(c_74, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_partfun1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_18])).
% 10.20/3.74  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.20/3.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.20/3.74  tff(c_58, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_157])).
% 10.20/3.74  tff(c_10910, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10904, c_58])).
% 10.20/3.74  tff(c_10920, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_72, c_10910])).
% 10.20/3.74  tff(c_24, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.74  tff(c_10954, plain, (v4_relat_1('#skF_2', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_10920, c_24])).
% 10.20/3.74  tff(c_14, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.20/3.74  tff(c_10960, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10954, c_14])).
% 10.20/3.74  tff(c_10963, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_10960])).
% 10.20/3.74  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.20/3.74  tff(c_10967, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10963, c_12])).
% 10.20/3.74  tff(c_10971, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_10904, c_10967])).
% 10.20/3.74  tff(c_11124, plain, (![A_596, B_597]: (k9_relat_1(k2_funct_1(A_596), k9_relat_1(A_596, B_597))=B_597 | ~r1_tarski(B_597, k1_relat_1(A_596)) | ~v2_funct_1(A_596) | ~v1_funct_1(A_596) | ~v1_relat_1(A_596))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.20/3.74  tff(c_11142, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10971, c_11124])).
% 10.20/3.74  tff(c_11154, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_72, c_11091, c_6, c_11142])).
% 10.20/3.74  tff(c_16, plain, (![A_12, B_14]: (k9_relat_1(k2_funct_1(A_12), k9_relat_1(A_12, B_14))=B_14 | ~r1_tarski(B_14, k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.20/3.74  tff(c_11162, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11154, c_16])).
% 10.20/3.74  tff(c_11168, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_11162])).
% 10.20/3.74  tff(c_11370, plain, (![A_614, B_615]: (k2_funct_2(A_614, B_615)=k2_funct_1(B_615) | ~m1_subset_1(B_615, k1_zfmisc_1(k2_zfmisc_1(A_614, A_614))) | ~v3_funct_2(B_615, A_614, A_614) | ~v1_funct_2(B_615, A_614, A_614) | ~v1_funct_1(B_615))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_11376, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_11370])).
% 10.20/3.74  tff(c_11380, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_11376])).
% 10.20/3.74  tff(c_11589, plain, (![A_632, B_633]: (m1_subset_1(k2_funct_2(A_632, B_633), k1_zfmisc_1(k2_zfmisc_1(A_632, A_632))) | ~m1_subset_1(B_633, k1_zfmisc_1(k2_zfmisc_1(A_632, A_632))) | ~v3_funct_2(B_633, A_632, A_632) | ~v1_funct_2(B_633, A_632, A_632) | ~v1_funct_1(B_633))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_11619, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11380, c_11589])).
% 10.20/3.74  tff(c_11633, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_11619])).
% 10.20/3.74  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.20/3.74  tff(c_11660, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_11633, c_8])).
% 10.20/3.74  tff(c_11684, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11660])).
% 10.20/3.74  tff(c_11686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11168, c_11684])).
% 10.20/3.74  tff(c_11688, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_11162])).
% 10.20/3.74  tff(c_12601, plain, (![A_691, B_692]: (k2_funct_2(A_691, B_692)=k2_funct_1(B_692) | ~m1_subset_1(B_692, k1_zfmisc_1(k2_zfmisc_1(A_691, A_691))) | ~v3_funct_2(B_692, A_691, A_691) | ~v1_funct_2(B_692, A_691, A_691) | ~v1_funct_1(B_692))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_12607, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_12601])).
% 10.20/3.74  tff(c_12611, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_12607])).
% 10.20/3.74  tff(c_12276, plain, (![A_670, B_671]: (v1_funct_1(k2_funct_2(A_670, B_671)) | ~m1_subset_1(B_671, k1_zfmisc_1(k2_zfmisc_1(A_670, A_670))) | ~v3_funct_2(B_671, A_670, A_670) | ~v1_funct_2(B_671, A_670, A_670) | ~v1_funct_1(B_671))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_12282, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_12276])).
% 10.20/3.74  tff(c_12286, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_12282])).
% 10.20/3.74  tff(c_12612, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12611, c_12286])).
% 10.20/3.74  tff(c_12637, plain, (![A_693, B_694]: (v3_funct_2(k2_funct_2(A_693, B_694), A_693, A_693) | ~m1_subset_1(B_694, k1_zfmisc_1(k2_zfmisc_1(A_693, A_693))) | ~v3_funct_2(B_694, A_693, A_693) | ~v1_funct_2(B_694, A_693, A_693) | ~v1_funct_1(B_694))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_12641, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_12637])).
% 10.20/3.74  tff(c_12645, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_12611, c_12641])).
% 10.20/3.74  tff(c_12819, plain, (![A_697, B_698]: (m1_subset_1(k2_funct_2(A_697, B_698), k1_zfmisc_1(k2_zfmisc_1(A_697, A_697))) | ~m1_subset_1(B_698, k1_zfmisc_1(k2_zfmisc_1(A_697, A_697))) | ~v3_funct_2(B_698, A_697, A_697) | ~v1_funct_2(B_698, A_697, A_697) | ~v1_funct_1(B_698))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_12849, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12611, c_12819])).
% 10.20/3.74  tff(c_12863, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_12849])).
% 10.20/3.74  tff(c_30, plain, (![C_25, B_24, A_23]: (v2_funct_2(C_25, B_24) | ~v3_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.74  tff(c_12876, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12863, c_30])).
% 10.20/3.74  tff(c_12905, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12612, c_12645, c_12876])).
% 10.20/3.74  tff(c_22, plain, (![C_18, B_17, A_16]: (v5_relat_1(C_18, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.74  tff(c_12910, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_12863, c_22])).
% 10.20/3.74  tff(c_38, plain, (![B_27, A_26]: (k2_relat_1(B_27)=A_26 | ~v2_funct_2(B_27, A_26) | ~v5_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.20/3.74  tff(c_12917, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12910, c_38])).
% 10.20/3.74  tff(c_12920, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11688, c_12905, c_12917])).
% 10.20/3.74  tff(c_12911, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_12863, c_24])).
% 10.20/3.74  tff(c_12923, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12911, c_14])).
% 10.20/3.74  tff(c_12926, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11688, c_12923])).
% 10.20/3.74  tff(c_11897, plain, (![A_651, B_652]: (k2_funct_2(A_651, B_652)=k2_funct_1(B_652) | ~m1_subset_1(B_652, k1_zfmisc_1(k2_zfmisc_1(A_651, A_651))) | ~v3_funct_2(B_652, A_651, A_651) | ~v1_funct_2(B_652, A_651, A_651) | ~v1_funct_1(B_652))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_11903, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_11897])).
% 10.20/3.74  tff(c_11907, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_11903])).
% 10.20/3.74  tff(c_12118, plain, (![A_668, B_669]: (m1_subset_1(k2_funct_2(A_668, B_669), k1_zfmisc_1(k2_zfmisc_1(A_668, A_668))) | ~m1_subset_1(B_669, k1_zfmisc_1(k2_zfmisc_1(A_668, A_668))) | ~v3_funct_2(B_669, A_668, A_668) | ~v1_funct_2(B_669, A_668, A_668) | ~v1_funct_1(B_669))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_12148, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11907, c_12118])).
% 10.20/3.74  tff(c_12162, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_12148])).
% 10.20/3.74  tff(c_12210, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_12162, c_24])).
% 10.20/3.74  tff(c_12222, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12210, c_14])).
% 10.20/3.74  tff(c_12225, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11688, c_12222])).
% 10.20/3.74  tff(c_10797, plain, (![A_563]: (m1_subset_1(A_563, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_563), k2_relat_1(A_563)))) | ~v1_funct_1(A_563) | ~v1_relat_1(A_563))), inference(cnfTransformation, [status(thm)], [f_157])).
% 10.20/3.74  tff(c_10982, plain, (![A_581]: (v5_relat_1(A_581, k2_relat_1(A_581)) | ~v1_funct_1(A_581) | ~v1_relat_1(A_581))), inference(resolution, [status(thm)], [c_10797, c_22])).
% 10.20/3.74  tff(c_11710, plain, (![B_636, A_637]: (v5_relat_1(k7_relat_1(B_636, A_637), k9_relat_1(B_636, A_637)) | ~v1_funct_1(k7_relat_1(B_636, A_637)) | ~v1_relat_1(k7_relat_1(B_636, A_637)) | ~v1_relat_1(B_636))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10982])).
% 10.20/3.74  tff(c_11719, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11154, c_11710])).
% 10.20/3.74  tff(c_11749, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11688, c_11719])).
% 10.20/3.74  tff(c_11854, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_11749])).
% 10.20/3.74  tff(c_12270, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12225, c_11854])).
% 10.20/3.74  tff(c_12273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11688, c_12270])).
% 10.20/3.74  tff(c_12275, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_11749])).
% 10.20/3.74  tff(c_12321, plain, (![A_675, B_676]: (k2_funct_2(A_675, B_676)=k2_funct_1(B_676) | ~m1_subset_1(B_676, k1_zfmisc_1(k2_zfmisc_1(A_675, A_675))) | ~v3_funct_2(B_676, A_675, A_675) | ~v1_funct_2(B_676, A_675, A_675) | ~v1_funct_1(B_676))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_12327, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_12321])).
% 10.20/3.74  tff(c_12331, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_12327])).
% 10.20/3.74  tff(c_12332, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12331, c_12286])).
% 10.20/3.74  tff(c_12486, plain, (![A_689, B_690]: (m1_subset_1(k2_funct_2(A_689, B_690), k1_zfmisc_1(k2_zfmisc_1(A_689, A_689))) | ~m1_subset_1(B_690, k1_zfmisc_1(k2_zfmisc_1(A_689, A_689))) | ~v3_funct_2(B_690, A_689, A_689) | ~v1_funct_2(B_690, A_689, A_689) | ~v1_funct_1(B_690))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_12516, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12331, c_12486])).
% 10.20/3.74  tff(c_12530, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_12516])).
% 10.20/3.74  tff(c_12578, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_12530, c_24])).
% 10.20/3.74  tff(c_12590, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_12578, c_14])).
% 10.20/3.74  tff(c_12593, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11688, c_12590])).
% 10.20/3.74  tff(c_12274, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_11749])).
% 10.20/3.74  tff(c_12287, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_12274])).
% 10.20/3.74  tff(c_12594, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12593, c_12287])).
% 10.20/3.74  tff(c_12598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12332, c_12594])).
% 10.20/3.74  tff(c_12599, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_12274])).
% 10.20/3.74  tff(c_12622, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2') | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_12599, c_38])).
% 10.20/3.74  tff(c_12625, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2') | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12275, c_12622])).
% 10.20/3.74  tff(c_12631, plain, (~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_12625])).
% 10.20/3.74  tff(c_12600, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_12274])).
% 10.20/3.74  tff(c_36, plain, (![B_27]: (v2_funct_2(B_27, k2_relat_1(B_27)) | ~v5_relat_1(B_27, k2_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.20/3.74  tff(c_11001, plain, (![A_583]: (v2_funct_2(A_583, k2_relat_1(A_583)) | ~v1_funct_1(A_583) | ~v1_relat_1(A_583))), inference(resolution, [status(thm)], [c_10982, c_36])).
% 10.20/3.74  tff(c_11806, plain, (![B_644, A_645]: (v2_funct_2(k7_relat_1(B_644, A_645), k9_relat_1(B_644, A_645)) | ~v1_funct_1(k7_relat_1(B_644, A_645)) | ~v1_relat_1(k7_relat_1(B_644, A_645)) | ~v1_relat_1(B_644))), inference(superposition, [status(thm), theory('equality')], [c_12, c_11001])).
% 10.20/3.74  tff(c_11812, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11154, c_11806])).
% 10.20/3.74  tff(c_11841, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11688, c_11812])).
% 10.20/3.74  tff(c_12633, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12275, c_12600, c_11841])).
% 10.20/3.74  tff(c_12634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12631, c_12633])).
% 10.20/3.74  tff(c_12635, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_12625])).
% 10.20/3.74  tff(c_12978, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12926, c_12635])).
% 10.20/3.74  tff(c_12982, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12920, c_12978])).
% 10.20/3.74  tff(c_10699, plain, (![C_543, A_544, B_545]: (v4_relat_1(C_543, A_544) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.74  tff(c_10707, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_10699])).
% 10.20/3.74  tff(c_10709, plain, (![B_547, A_548]: (k7_relat_1(B_547, A_548)=B_547 | ~v4_relat_1(B_547, A_548) | ~v1_relat_1(B_547))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.20/3.74  tff(c_10715, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10707, c_10709])).
% 10.20/3.74  tff(c_10721, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_10715])).
% 10.20/3.74  tff(c_10725, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10721, c_12])).
% 10.20/3.74  tff(c_10729, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_10725])).
% 10.20/3.74  tff(c_10906, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10904, c_10729])).
% 10.20/3.74  tff(c_11145, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10906, c_11124])).
% 10.20/3.74  tff(c_11156, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10688, c_72, c_11091, c_11145])).
% 10.20/3.74  tff(c_11166, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11154, c_11156])).
% 10.20/3.74  tff(c_11167, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_11166])).
% 10.20/3.74  tff(c_13004, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12982, c_11167])).
% 10.20/3.74  tff(c_13014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13004])).
% 10.20/3.74  tff(c_13015, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_11166])).
% 10.20/3.74  tff(c_13193, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13015, c_11162])).
% 10.20/3.74  tff(c_13194, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_13193])).
% 10.20/3.74  tff(c_13261, plain, (![A_716, B_717]: (k2_funct_2(A_716, B_717)=k2_funct_1(B_717) | ~m1_subset_1(B_717, k1_zfmisc_1(k2_zfmisc_1(A_716, A_716))) | ~v3_funct_2(B_717, A_716, A_716) | ~v1_funct_2(B_717, A_716, A_716) | ~v1_funct_1(B_717))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_13267, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_13261])).
% 10.20/3.74  tff(c_13271, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_13267])).
% 10.20/3.74  tff(c_13402, plain, (![A_731, B_732]: (m1_subset_1(k2_funct_2(A_731, B_732), k1_zfmisc_1(k2_zfmisc_1(A_731, A_731))) | ~m1_subset_1(B_732, k1_zfmisc_1(k2_zfmisc_1(A_731, A_731))) | ~v3_funct_2(B_732, A_731, A_731) | ~v1_funct_2(B_732, A_731, A_731) | ~v1_funct_1(B_732))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_13432, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13271, c_13402])).
% 10.20/3.74  tff(c_13446, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_13432])).
% 10.20/3.74  tff(c_13473, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_13446, c_8])).
% 10.20/3.74  tff(c_13497, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_13473])).
% 10.20/3.74  tff(c_13499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13194, c_13497])).
% 10.20/3.74  tff(c_13501, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_13193])).
% 10.20/3.74  tff(c_13045, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13015, c_11154])).
% 10.20/3.74  tff(c_13101, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13045, c_16])).
% 10.20/3.74  tff(c_14178, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13501, c_13101])).
% 10.20/3.74  tff(c_14179, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_14178])).
% 10.20/3.74  tff(c_14242, plain, (![A_779, B_780]: (k2_funct_2(A_779, B_780)=k2_funct_1(B_780) | ~m1_subset_1(B_780, k1_zfmisc_1(k2_zfmisc_1(A_779, A_779))) | ~v3_funct_2(B_780, A_779, A_779) | ~v1_funct_2(B_780, A_779, A_779) | ~v1_funct_1(B_780))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_14248, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_14242])).
% 10.20/3.74  tff(c_14252, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_14248])).
% 10.20/3.74  tff(c_13181, plain, (![A_708, B_709]: (v1_funct_1(k2_funct_2(A_708, B_709)) | ~m1_subset_1(B_709, k1_zfmisc_1(k2_zfmisc_1(A_708, A_708))) | ~v3_funct_2(B_709, A_708, A_708) | ~v1_funct_2(B_709, A_708, A_708) | ~v1_funct_1(B_709))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_13187, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_13181])).
% 10.20/3.74  tff(c_13191, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_13187])).
% 10.20/3.74  tff(c_14253, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14252, c_13191])).
% 10.20/3.74  tff(c_14258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14179, c_14253])).
% 10.20/3.74  tff(c_14260, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_14178])).
% 10.20/3.74  tff(c_14326, plain, (![A_781, B_782]: (k2_funct_2(A_781, B_782)=k2_funct_1(B_782) | ~m1_subset_1(B_782, k1_zfmisc_1(k2_zfmisc_1(A_781, A_781))) | ~v3_funct_2(B_782, A_781, A_781) | ~v1_funct_2(B_782, A_781, A_781) | ~v1_funct_1(B_782))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_14332, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_14326])).
% 10.20/3.74  tff(c_14336, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_14332])).
% 10.20/3.74  tff(c_40, plain, (![A_28, B_29]: (m1_subset_1(k2_funct_2(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_14837, plain, (![D_794, A_797, E_796, B_795, C_799, F_798]: (k1_partfun1(A_797, B_795, C_799, D_794, E_796, F_798)=k5_relat_1(E_796, F_798) | ~m1_subset_1(F_798, k1_zfmisc_1(k2_zfmisc_1(C_799, D_794))) | ~v1_funct_1(F_798) | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(A_797, B_795))) | ~v1_funct_1(E_796))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.20/3.74  tff(c_14847, plain, (![A_797, B_795, E_796]: (k1_partfun1(A_797, B_795, '#skF_1', '#skF_1', E_796, '#skF_2')=k5_relat_1(E_796, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_796, k1_zfmisc_1(k2_zfmisc_1(A_797, B_795))) | ~v1_funct_1(E_796))), inference(resolution, [status(thm)], [c_66, c_14837])).
% 10.20/3.74  tff(c_14879, plain, (![A_800, B_801, E_802]: (k1_partfun1(A_800, B_801, '#skF_1', '#skF_1', E_802, '#skF_2')=k5_relat_1(E_802, '#skF_2') | ~m1_subset_1(E_802, k1_zfmisc_1(k2_zfmisc_1(A_800, B_801))) | ~v1_funct_1(E_802))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14847])).
% 10.20/3.74  tff(c_15263, plain, (![A_810, B_811]: (k1_partfun1(A_810, A_810, '#skF_1', '#skF_1', k2_funct_2(A_810, B_811), '#skF_2')=k5_relat_1(k2_funct_2(A_810, B_811), '#skF_2') | ~v1_funct_1(k2_funct_2(A_810, B_811)) | ~m1_subset_1(B_811, k1_zfmisc_1(k2_zfmisc_1(A_810, A_810))) | ~v3_funct_2(B_811, A_810, A_810) | ~v1_funct_2(B_811, A_810, A_810) | ~v1_funct_1(B_811))), inference(resolution, [status(thm)], [c_40, c_14879])).
% 10.20/3.74  tff(c_15273, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_15263])).
% 10.20/3.74  tff(c_15284, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_14260, c_14336, c_14336, c_14336, c_15273])).
% 10.20/3.74  tff(c_97, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.20/3.74  tff(c_103, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_97])).
% 10.20/3.74  tff(c_109, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_103])).
% 10.20/3.74  tff(c_503, plain, (![C_100, A_101, B_102]: (v2_funct_1(C_100) | ~v3_funct_2(C_100, A_101, B_102) | ~v1_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.74  tff(c_515, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_503])).
% 10.20/3.74  tff(c_523, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_515])).
% 10.20/3.74  tff(c_197, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.20/3.74  tff(c_202, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_50, c_197])).
% 10.20/3.74  tff(c_111, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.74  tff(c_119, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_111])).
% 10.20/3.74  tff(c_205, plain, (![B_72, A_73]: (k2_relat_1(B_72)=A_73 | ~v2_funct_2(B_72, A_73) | ~v5_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.20/3.74  tff(c_211, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_119, c_205])).
% 10.20/3.74  tff(c_217, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_211])).
% 10.20/3.74  tff(c_218, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_217])).
% 10.20/3.74  tff(c_326, plain, (![C_89, B_90, A_91]: (v2_funct_2(C_89, B_90) | ~v3_funct_2(C_89, A_91, B_90) | ~v1_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.74  tff(c_335, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_326])).
% 10.20/3.74  tff(c_340, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_335])).
% 10.20/3.74  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_340])).
% 10.20/3.74  tff(c_343, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_217])).
% 10.20/3.74  tff(c_365, plain, (![A_92]: (m1_subset_1(A_92, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_92), k2_relat_1(A_92)))) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_157])).
% 10.20/3.74  tff(c_379, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_343, c_365])).
% 10.20/3.74  tff(c_390, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_379])).
% 10.20/3.74  tff(c_403, plain, (v4_relat_1('#skF_2', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_390, c_24])).
% 10.20/3.74  tff(c_411, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_403, c_14])).
% 10.20/3.74  tff(c_414, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_411])).
% 10.20/3.74  tff(c_418, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_414, c_12])).
% 10.20/3.74  tff(c_422, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_343, c_418])).
% 10.20/3.74  tff(c_585, plain, (![A_111, B_112]: (k9_relat_1(k2_funct_1(A_111), k9_relat_1(A_111, B_112))=B_112 | ~r1_tarski(B_112, k1_relat_1(A_111)) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.20/3.74  tff(c_603, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_422, c_585])).
% 10.20/3.74  tff(c_615, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_523, c_6, c_603])).
% 10.20/3.74  tff(c_428, plain, (![A_93]: (v5_relat_1(A_93, k2_relat_1(A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_365, c_22])).
% 10.20/3.74  tff(c_648, plain, (![B_114, A_115]: (v5_relat_1(k7_relat_1(B_114, A_115), k9_relat_1(B_114, A_115)) | ~v1_funct_1(k7_relat_1(B_114, A_115)) | ~v1_relat_1(k7_relat_1(B_114, A_115)) | ~v1_relat_1(B_114))), inference(superposition, [status(thm), theory('equality')], [c_12, c_428])).
% 10.20/3.74  tff(c_657, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_648])).
% 10.20/3.74  tff(c_782, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_657])).
% 10.20/3.74  tff(c_823, plain, (![A_128, B_129]: (k2_funct_2(A_128, B_129)=k2_funct_1(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1(A_128, A_128))) | ~v3_funct_2(B_129, A_128, A_128) | ~v1_funct_2(B_129, A_128, A_128) | ~v1_funct_1(B_129))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_829, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_823])).
% 10.20/3.74  tff(c_833, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_829])).
% 10.20/3.74  tff(c_982, plain, (![A_143, B_144]: (m1_subset_1(k2_funct_2(A_143, B_144), k1_zfmisc_1(k2_zfmisc_1(A_143, A_143))) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(A_143, A_143))) | ~v3_funct_2(B_144, A_143, A_143) | ~v1_funct_2(B_144, A_143, A_143) | ~v1_funct_1(B_144))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_1012, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_833, c_982])).
% 10.20/3.74  tff(c_1026, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_1012])).
% 10.20/3.74  tff(c_1053, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1026, c_8])).
% 10.20/3.74  tff(c_1077, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1053])).
% 10.20/3.74  tff(c_1079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_782, c_1077])).
% 10.20/3.74  tff(c_1081, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_657])).
% 10.20/3.74  tff(c_624, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_16])).
% 10.20/3.74  tff(c_1701, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_624])).
% 10.20/3.74  tff(c_1702, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1701])).
% 10.20/3.74  tff(c_1746, plain, (![A_186, B_187]: (k2_funct_2(A_186, B_187)=k2_funct_1(B_187) | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_187, A_186, A_186) | ~v1_funct_2(B_187, A_186, A_186) | ~v1_funct_1(B_187))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_1752, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1746])).
% 10.20/3.74  tff(c_1756, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1752])).
% 10.20/3.74  tff(c_1734, plain, (![A_183, B_184]: (v1_funct_1(k2_funct_2(A_183, B_184)) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_1740, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1734])).
% 10.20/3.74  tff(c_1744, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1740])).
% 10.20/3.74  tff(c_1757, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_1744])).
% 10.20/3.74  tff(c_1760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1702, c_1757])).
% 10.20/3.74  tff(c_1762, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1701])).
% 10.20/3.74  tff(c_2173, plain, (![A_209, B_210]: (k2_funct_2(A_209, B_210)=k2_funct_1(B_210) | ~m1_subset_1(B_210, k1_zfmisc_1(k2_zfmisc_1(A_209, A_209))) | ~v3_funct_2(B_210, A_209, A_209) | ~v1_funct_2(B_210, A_209, A_209) | ~v1_funct_1(B_210))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_2179, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2173])).
% 10.20/3.74  tff(c_2183, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2179])).
% 10.20/3.74  tff(c_2230, plain, (![A_211, B_212]: (v3_funct_2(k2_funct_2(A_211, B_212), A_211, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(k2_zfmisc_1(A_211, A_211))) | ~v3_funct_2(B_212, A_211, A_211) | ~v1_funct_2(B_212, A_211, A_211) | ~v1_funct_1(B_212))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_2234, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2230])).
% 10.20/3.74  tff(c_2238, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2183, c_2234])).
% 10.20/3.74  tff(c_3122, plain, (![A_259, B_260]: (m1_subset_1(k2_funct_2(A_259, B_260), k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_3152, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2183, c_3122])).
% 10.20/3.74  tff(c_3166, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_3152])).
% 10.20/3.74  tff(c_3179, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3166, c_30])).
% 10.20/3.74  tff(c_3208, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_2238, c_3179])).
% 10.20/3.74  tff(c_3213, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3166, c_24])).
% 10.20/3.74  tff(c_3220, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3213, c_14])).
% 10.20/3.74  tff(c_3223, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_3220])).
% 10.20/3.74  tff(c_1126, plain, (![A_150, B_151]: (k2_funct_2(A_150, B_151)=k2_funct_1(B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(k2_zfmisc_1(A_150, A_150))) | ~v3_funct_2(B_151, A_150, A_150) | ~v1_funct_2(B_151, A_150, A_150) | ~v1_funct_1(B_151))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_1132, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1126])).
% 10.20/3.74  tff(c_1136, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1132])).
% 10.20/3.74  tff(c_1517, plain, (![A_174, B_175]: (m1_subset_1(k2_funct_2(A_174, B_175), k1_zfmisc_1(k2_zfmisc_1(A_174, A_174))) | ~m1_subset_1(B_175, k1_zfmisc_1(k2_zfmisc_1(A_174, A_174))) | ~v3_funct_2(B_175, A_174, A_174) | ~v1_funct_2(B_175, A_174, A_174) | ~v1_funct_1(B_175))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_1547, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1136, c_1517])).
% 10.20/3.74  tff(c_1561, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_1547])).
% 10.20/3.74  tff(c_1608, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1561, c_24])).
% 10.20/3.74  tff(c_1615, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1608, c_14])).
% 10.20/3.74  tff(c_1618, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1615])).
% 10.20/3.74  tff(c_461, plain, (![A_97]: (v2_funct_2(A_97, k2_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_428, c_36])).
% 10.20/3.74  tff(c_736, plain, (![B_122, A_123]: (v2_funct_2(k7_relat_1(B_122, A_123), k9_relat_1(B_122, A_123)) | ~v1_funct_1(k7_relat_1(B_122, A_123)) | ~v1_relat_1(k7_relat_1(B_122, A_123)) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_12, c_461])).
% 10.20/3.74  tff(c_742, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_736])).
% 10.20/3.74  tff(c_1083, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_742])).
% 10.20/3.74  tff(c_1084, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_1083])).
% 10.20/3.74  tff(c_1694, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1084])).
% 10.20/3.74  tff(c_1697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1081, c_1694])).
% 10.20/3.74  tff(c_1699, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_1083])).
% 10.20/3.74  tff(c_1778, plain, (![A_190, B_191]: (k2_funct_2(A_190, B_191)=k2_funct_1(B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_1784, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1778])).
% 10.20/3.74  tff(c_1788, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1784])).
% 10.20/3.74  tff(c_1917, plain, (![A_205, B_206]: (m1_subset_1(k2_funct_2(A_205, B_206), k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_1947, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1788, c_1917])).
% 10.20/3.74  tff(c_1961, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_1947])).
% 10.20/3.74  tff(c_2008, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1961, c_24])).
% 10.20/3.74  tff(c_2015, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2008, c_14])).
% 10.20/3.74  tff(c_2018, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_2015])).
% 10.20/3.74  tff(c_1698, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1083])).
% 10.20/3.74  tff(c_1763, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_1698])).
% 10.20/3.74  tff(c_2025, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2018, c_1763])).
% 10.20/3.74  tff(c_2029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1762, c_2025])).
% 10.20/3.74  tff(c_2030, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1698])).
% 10.20/3.74  tff(c_2031, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_1698])).
% 10.20/3.74  tff(c_1080, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_657])).
% 10.20/3.74  tff(c_2045, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_1699, c_1080])).
% 10.20/3.74  tff(c_2048, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2') | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_2045, c_38])).
% 10.20/3.74  tff(c_2051, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_2030, c_2048])).
% 10.20/3.74  tff(c_3241, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3223, c_2051])).
% 10.20/3.74  tff(c_3214, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3166, c_22])).
% 10.20/3.74  tff(c_3226, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3214, c_38])).
% 10.20/3.74  tff(c_3229, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_3226])).
% 10.20/3.74  tff(c_3449, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3208, c_3241, c_3229])).
% 10.20/3.74  tff(c_130, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.20/3.74  tff(c_138, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_130])).
% 10.20/3.74  tff(c_140, plain, (![B_62, A_63]: (k7_relat_1(B_62, A_63)=B_62 | ~v4_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.20/3.74  tff(c_146, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_138, c_140])).
% 10.20/3.74  tff(c_152, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_146])).
% 10.20/3.74  tff(c_156, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_152, c_12])).
% 10.20/3.74  tff(c_160, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_156])).
% 10.20/3.74  tff(c_345, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_343, c_160])).
% 10.20/3.74  tff(c_606, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_345, c_585])).
% 10.20/3.74  tff(c_617, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_523, c_606])).
% 10.20/3.74  tff(c_620, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_617])).
% 10.20/3.74  tff(c_3455, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_620])).
% 10.20/3.74  tff(c_3466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3455])).
% 10.20/3.74  tff(c_3467, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_617])).
% 10.20/3.74  tff(c_3502, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3467, c_615])).
% 10.20/3.74  tff(c_20, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.20/3.74  tff(c_73, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_partfun1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 10.20/3.74  tff(c_3578, plain, (![B_277, A_278]: (v5_relat_1(k7_relat_1(B_277, A_278), k9_relat_1(B_277, A_278)) | ~v1_funct_1(k7_relat_1(B_277, A_278)) | ~v1_relat_1(k7_relat_1(B_277, A_278)) | ~v1_relat_1(B_277))), inference(superposition, [status(thm), theory('equality')], [c_12, c_428])).
% 10.20/3.74  tff(c_3587, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3467, c_3578])).
% 10.20/3.74  tff(c_3681, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3587])).
% 10.20/3.74  tff(c_3711, plain, (![A_288, B_289]: (k2_funct_2(A_288, B_289)=k2_funct_1(B_289) | ~m1_subset_1(B_289, k1_zfmisc_1(k2_zfmisc_1(A_288, A_288))) | ~v3_funct_2(B_289, A_288, A_288) | ~v1_funct_2(B_289, A_288, A_288) | ~v1_funct_1(B_289))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_3717, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_3711])).
% 10.20/3.74  tff(c_3721, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_3717])).
% 10.20/3.74  tff(c_3889, plain, (![A_305, B_306]: (m1_subset_1(k2_funct_2(A_305, B_306), k1_zfmisc_1(k2_zfmisc_1(A_305, A_305))) | ~m1_subset_1(B_306, k1_zfmisc_1(k2_zfmisc_1(A_305, A_305))) | ~v3_funct_2(B_306, A_305, A_305) | ~v1_funct_2(B_306, A_305, A_305) | ~v1_funct_1(B_306))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_3919, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3721, c_3889])).
% 10.20/3.74  tff(c_3933, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_3919])).
% 10.20/3.74  tff(c_3960, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_3933, c_8])).
% 10.20/3.74  tff(c_3984, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3960])).
% 10.20/3.74  tff(c_3986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3681, c_3984])).
% 10.20/3.74  tff(c_3988, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3587])).
% 10.20/3.74  tff(c_5302, plain, (![A_377, B_378]: (k2_funct_2(A_377, B_378)=k2_funct_1(B_378) | ~m1_subset_1(B_378, k1_zfmisc_1(k2_zfmisc_1(A_377, A_377))) | ~v3_funct_2(B_378, A_377, A_377) | ~v1_funct_2(B_378, A_377, A_377) | ~v1_funct_1(B_378))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_5308, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_5302])).
% 10.20/3.74  tff(c_5312, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_5308])).
% 10.20/3.74  tff(c_3633, plain, (![A_281, B_282]: (v1_funct_1(k2_funct_2(A_281, B_282)) | ~m1_subset_1(B_282, k1_zfmisc_1(k2_zfmisc_1(A_281, A_281))) | ~v3_funct_2(B_282, A_281, A_281) | ~v1_funct_2(B_282, A_281, A_281) | ~v1_funct_1(B_282))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_3639, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_3633])).
% 10.20/3.74  tff(c_3643, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_3639])).
% 10.20/3.74  tff(c_5313, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5312, c_3643])).
% 10.20/3.74  tff(c_3498, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3467, c_16])).
% 10.20/3.74  tff(c_6011, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5313, c_3498])).
% 10.20/3.74  tff(c_6012, plain, (~v2_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_6011])).
% 10.20/3.74  tff(c_5941, plain, (![A_412, B_413]: (v3_funct_2(k2_funct_2(A_412, B_413), A_412, A_412) | ~m1_subset_1(B_413, k1_zfmisc_1(k2_zfmisc_1(A_412, A_412))) | ~v3_funct_2(B_413, A_412, A_412) | ~v1_funct_2(B_413, A_412, A_412) | ~v1_funct_1(B_413))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_5945, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_5941])).
% 10.20/3.74  tff(c_5949, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_5312, c_5945])).
% 10.20/3.74  tff(c_6063, plain, (![A_418, B_419]: (m1_subset_1(k2_funct_2(A_418, B_419), k1_zfmisc_1(k2_zfmisc_1(A_418, A_418))) | ~m1_subset_1(B_419, k1_zfmisc_1(k2_zfmisc_1(A_418, A_418))) | ~v3_funct_2(B_419, A_418, A_418) | ~v1_funct_2(B_419, A_418, A_418) | ~v1_funct_1(B_419))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_6093, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5312, c_6063])).
% 10.20/3.74  tff(c_6107, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_6093])).
% 10.20/3.74  tff(c_32, plain, (![C_25, A_23, B_24]: (v2_funct_1(C_25) | ~v3_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.20/3.74  tff(c_6123, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6107, c_32])).
% 10.20/3.74  tff(c_6152, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_5949, c_6123])).
% 10.20/3.74  tff(c_6154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6012, c_6152])).
% 10.20/3.74  tff(c_6156, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_6011])).
% 10.20/3.74  tff(c_6881, plain, (![A_441, B_442]: (v1_funct_2(k2_funct_2(A_441, B_442), A_441, A_441) | ~m1_subset_1(B_442, k1_zfmisc_1(k2_zfmisc_1(A_441, A_441))) | ~v3_funct_2(B_442, A_441, A_441) | ~v1_funct_2(B_442, A_441, A_441) | ~v1_funct_1(B_442))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_6885, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_6881])).
% 10.20/3.74  tff(c_6889, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_5312, c_6885])).
% 10.20/3.74  tff(c_7332, plain, (![A_459, B_460]: (m1_subset_1(k2_funct_2(A_459, B_460), k1_zfmisc_1(k2_zfmisc_1(A_459, A_459))) | ~m1_subset_1(B_460, k1_zfmisc_1(k2_zfmisc_1(A_459, A_459))) | ~v3_funct_2(B_460, A_459, A_459) | ~v1_funct_2(B_460, A_459, A_459) | ~v1_funct_1(B_460))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_7362, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5312, c_7332])).
% 10.20/3.74  tff(c_7376, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_7362])).
% 10.20/3.74  tff(c_54, plain, (![A_37, B_38]: (k2_funct_2(A_37, B_38)=k2_funct_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))) | ~v3_funct_2(B_38, A_37, A_37) | ~v1_funct_2(B_38, A_37, A_37) | ~v1_funct_1(B_38))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_7383, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7376, c_54])).
% 10.20/3.74  tff(c_7412, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6889, c_5949, c_7383])).
% 10.20/3.74  tff(c_46, plain, (![A_28, B_29]: (v1_funct_1(k2_funct_2(A_28, B_29)) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_7386, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7376, c_46])).
% 10.20/3.74  tff(c_7415, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6889, c_5949, c_7386])).
% 10.20/3.74  tff(c_7583, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7412, c_7415])).
% 10.20/3.74  tff(c_42, plain, (![A_28, B_29]: (v3_funct_2(k2_funct_2(A_28, B_29), A_28, A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_7380, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7376, c_42])).
% 10.20/3.74  tff(c_7409, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6889, c_5949, c_7380])).
% 10.20/3.74  tff(c_7582, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7412, c_7409])).
% 10.20/3.74  tff(c_7587, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7412, c_40])).
% 10.20/3.74  tff(c_7591, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6889, c_5949, c_7376, c_7587])).
% 10.20/3.74  tff(c_7645, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_7591, c_30])).
% 10.20/3.74  tff(c_7680, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7583, c_7582, c_7645])).
% 10.20/3.74  tff(c_7423, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_7376, c_24])).
% 10.20/3.74  tff(c_7430, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7423, c_14])).
% 10.20/3.74  tff(c_7433, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_7430])).
% 10.20/3.74  tff(c_6939, plain, (![A_445, B_446]: (m1_subset_1(k2_funct_2(A_445, B_446), k1_zfmisc_1(k2_zfmisc_1(A_445, A_445))) | ~m1_subset_1(B_446, k1_zfmisc_1(k2_zfmisc_1(A_445, A_445))) | ~v3_funct_2(B_446, A_445, A_445) | ~v1_funct_2(B_446, A_445, A_445) | ~v1_funct_1(B_446))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_6969, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5312, c_6939])).
% 10.20/3.74  tff(c_6983, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_6969])).
% 10.20/3.74  tff(c_7030, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_6983, c_24])).
% 10.20/3.74  tff(c_7037, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7030, c_14])).
% 10.20/3.74  tff(c_7040, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_7037])).
% 10.20/3.74  tff(c_6168, plain, (![A_420, B_421]: (v1_funct_2(k2_funct_2(A_420, B_421), A_420, A_420) | ~m1_subset_1(B_421, k1_zfmisc_1(k2_zfmisc_1(A_420, A_420))) | ~v3_funct_2(B_421, A_420, A_420) | ~v1_funct_2(B_421, A_420, A_420) | ~v1_funct_1(B_421))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_6172, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_6168])).
% 10.20/3.74  tff(c_6176, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_5312, c_6172])).
% 10.20/3.74  tff(c_6390, plain, (![A_426, B_427]: (m1_subset_1(k2_funct_2(A_426, B_427), k1_zfmisc_1(k2_zfmisc_1(A_426, A_426))) | ~m1_subset_1(B_427, k1_zfmisc_1(k2_zfmisc_1(A_426, A_426))) | ~v3_funct_2(B_427, A_426, A_426) | ~v1_funct_2(B_427, A_426, A_426) | ~v1_funct_1(B_427))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_6420, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5312, c_6390])).
% 10.20/3.74  tff(c_6434, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_6420])).
% 10.20/3.74  tff(c_6441, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6434, c_54])).
% 10.20/3.74  tff(c_6470, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6176, c_5949, c_6441])).
% 10.20/3.74  tff(c_6591, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6470, c_40])).
% 10.20/3.74  tff(c_6595, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6176, c_5949, c_6434, c_6591])).
% 10.20/3.74  tff(c_6712, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_6595, c_8])).
% 10.20/3.74  tff(c_6742, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6712])).
% 10.20/3.74  tff(c_6447, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6434, c_30])).
% 10.20/3.74  tff(c_6476, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_5949, c_6447])).
% 10.20/3.74  tff(c_6482, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_6434, c_22])).
% 10.20/3.74  tff(c_6494, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6482, c_38])).
% 10.20/3.74  tff(c_6497, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_6476, c_6494])).
% 10.20/3.74  tff(c_446, plain, (![A_94]: (v4_relat_1(A_94, k1_relat_1(A_94)) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_365, c_24])).
% 10.20/3.74  tff(c_470, plain, (![A_98]: (k7_relat_1(A_98, k1_relat_1(A_98))=A_98 | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_446, c_14])).
% 10.20/3.74  tff(c_479, plain, (![A_98]: (k9_relat_1(A_98, k1_relat_1(A_98))=k2_relat_1(A_98) | ~v1_relat_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_470, c_12])).
% 10.20/3.74  tff(c_600, plain, (![A_98]: (k9_relat_1(k2_funct_1(A_98), k2_relat_1(A_98))=k1_relat_1(A_98) | ~r1_tarski(k1_relat_1(A_98), k1_relat_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98) | ~v1_relat_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_479, c_585])).
% 10.20/3.74  tff(c_613, plain, (![A_98]: (k9_relat_1(k2_funct_1(A_98), k2_relat_1(A_98))=k1_relat_1(A_98) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_600])).
% 10.20/3.74  tff(c_6501, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6497, c_613])).
% 10.20/3.74  tff(c_6526, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5313, c_6156, c_6501])).
% 10.20/3.74  tff(c_6444, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6434, c_46])).
% 10.20/3.74  tff(c_6473, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6176, c_5949, c_6444])).
% 10.20/3.74  tff(c_6587, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6473])).
% 10.20/3.74  tff(c_6438, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6434, c_42])).
% 10.20/3.74  tff(c_6467, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6176, c_5949, c_6438])).
% 10.20/3.74  tff(c_6617, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6470, c_6467])).
% 10.20/3.74  tff(c_6698, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_6595, c_30])).
% 10.20/3.74  tff(c_6733, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6587, c_6617, c_6698])).
% 10.20/3.74  tff(c_6739, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_6595, c_22])).
% 10.20/3.74  tff(c_6755, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_6739, c_38])).
% 10.20/3.74  tff(c_6758, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_6733, c_6755])).
% 10.20/3.74  tff(c_6738, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_6595, c_24])).
% 10.20/3.74  tff(c_6749, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_6738, c_14])).
% 10.20/3.74  tff(c_6752, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_6749])).
% 10.20/3.74  tff(c_6859, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_6752, c_12])).
% 10.20/3.74  tff(c_6867, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_6526, c_6758, c_6859])).
% 10.20/3.74  tff(c_6481, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_6434, c_24])).
% 10.20/3.74  tff(c_6488, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6481, c_14])).
% 10.20/3.74  tff(c_6491, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_6488])).
% 10.20/3.74  tff(c_5619, plain, (![A_400, B_401]: (m1_subset_1(k2_funct_2(A_400, B_401), k1_zfmisc_1(k2_zfmisc_1(A_400, A_400))) | ~m1_subset_1(B_401, k1_zfmisc_1(k2_zfmisc_1(A_400, A_400))) | ~v3_funct_2(B_401, A_400, A_400) | ~v1_funct_2(B_401, A_400, A_400) | ~v1_funct_1(B_401))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_5649, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5312, c_5619])).
% 10.20/3.74  tff(c_5663, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_5649])).
% 10.20/3.74  tff(c_5710, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_5663, c_24])).
% 10.20/3.74  tff(c_5717, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5710, c_14])).
% 10.20/3.74  tff(c_5720, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5717])).
% 10.20/3.74  tff(c_4575, plain, (![A_343, B_344]: (k2_funct_2(A_343, B_344)=k2_funct_1(B_344) | ~m1_subset_1(B_344, k1_zfmisc_1(k2_zfmisc_1(A_343, A_343))) | ~v3_funct_2(B_344, A_343, A_343) | ~v1_funct_2(B_344, A_343, A_343) | ~v1_funct_1(B_344))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.20/3.74  tff(c_4581, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_4575])).
% 10.20/3.74  tff(c_4585, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_4581])).
% 10.20/3.74  tff(c_4586, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4585, c_3643])).
% 10.20/3.74  tff(c_5117, plain, (![A_375, B_376]: (m1_subset_1(k2_funct_2(A_375, B_376), k1_zfmisc_1(k2_zfmisc_1(A_375, A_375))) | ~m1_subset_1(B_376, k1_zfmisc_1(k2_zfmisc_1(A_375, A_375))) | ~v3_funct_2(B_376, A_375, A_375) | ~v1_funct_2(B_376, A_375, A_375) | ~v1_funct_1(B_376))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_5147, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4585, c_5117])).
% 10.20/3.74  tff(c_5161, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_5147])).
% 10.20/3.74  tff(c_5273, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_5161, c_24])).
% 10.20/3.74  tff(c_5280, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_5273, c_14])).
% 10.20/3.74  tff(c_5283, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5280])).
% 10.20/3.74  tff(c_3987, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_3587])).
% 10.20/3.74  tff(c_3989, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_3987])).
% 10.20/3.74  tff(c_5293, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5283, c_3989])).
% 10.20/3.74  tff(c_5299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4586, c_5293])).
% 10.20/3.74  tff(c_5300, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_3987])).
% 10.20/3.74  tff(c_5319, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_5300])).
% 10.20/3.74  tff(c_5791, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5720, c_5319])).
% 10.20/3.74  tff(c_5795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5791])).
% 10.20/3.74  tff(c_5797, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_5300])).
% 10.20/3.74  tff(c_5301, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_3987])).
% 10.20/3.74  tff(c_5796, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_5300])).
% 10.20/3.74  tff(c_5800, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_5796, c_38])).
% 10.20/3.74  tff(c_5803, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5797, c_5800])).
% 10.20/3.74  tff(c_5804, plain, (~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5803])).
% 10.20/3.74  tff(c_3644, plain, (![B_283, A_284]: (v2_funct_2(k7_relat_1(B_283, A_284), k9_relat_1(B_283, A_284)) | ~v1_funct_1(k7_relat_1(B_283, A_284)) | ~v1_relat_1(k7_relat_1(B_283, A_284)) | ~v1_relat_1(B_283))), inference(superposition, [status(thm), theory('equality')], [c_12, c_461])).
% 10.20/3.74  tff(c_3650, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3467, c_3644])).
% 10.20/3.74  tff(c_5844, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5797, c_5301, c_3650])).
% 10.20/3.74  tff(c_5845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5804, c_5844])).
% 10.20/3.74  tff(c_5846, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_5803])).
% 10.20/3.74  tff(c_519, plain, (![A_40]: (v2_funct_1(A_40) | ~v3_funct_2(A_40, k1_relat_1(A_40), k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_58, c_503])).
% 10.20/3.74  tff(c_5856, plain, (v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v3_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5846, c_519])).
% 10.20/3.74  tff(c_5886, plain, (v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v3_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5797, c_5301, c_5856])).
% 10.20/3.74  tff(c_6167, plain, (~v3_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')), inference(splitLeft, [status(thm)], [c_5886])).
% 10.20/3.74  tff(c_6544, plain, (~v3_funct_2(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6491, c_6491, c_6167])).
% 10.20/3.74  tff(c_6871, plain, (~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_6544])).
% 10.20/3.74  tff(c_6878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5949, c_6871])).
% 10.20/3.74  tff(c_6879, plain, (v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_5886])).
% 10.20/3.74  tff(c_5853, plain, (k9_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5846, c_613])).
% 10.20/3.74  tff(c_5884, plain, (k9_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5797, c_5301, c_5853])).
% 10.20/3.74  tff(c_6893, plain, (k9_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')=k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6879, c_5884])).
% 10.20/3.74  tff(c_467, plain, (![B_9, A_8]: (v2_funct_2(k7_relat_1(B_9, A_8), k9_relat_1(B_9, A_8)) | ~v1_funct_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_461])).
% 10.20/3.74  tff(c_6897, plain, (v2_funct_2(k7_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1'), k1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))) | ~v1_funct_1(k7_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')), '#skF_1')) | ~v1_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6893, c_467])).
% 10.20/3.74  tff(c_6907, plain, (~v1_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')))), inference(splitLeft, [status(thm)], [c_6897])).
% 10.20/3.74  tff(c_7091, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7040, c_6907])).
% 10.20/3.74  tff(c_6990, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6983, c_54])).
% 10.20/3.74  tff(c_7019, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6889, c_5949, c_6990])).
% 10.20/3.74  tff(c_7194, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7019, c_40])).
% 10.20/3.74  tff(c_7198, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_6889, c_5949, c_6983, c_7194])).
% 10.20/3.74  tff(c_7266, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_7198, c_8])).
% 10.20/3.74  tff(c_7296, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7266])).
% 10.20/3.74  tff(c_7298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7091, c_7296])).
% 10.20/3.74  tff(c_7300, plain, (v1_relat_1(k2_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_6897])).
% 10.20/3.74  tff(c_7484, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7433, c_7300])).
% 10.20/3.74  tff(c_7389, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7376, c_30])).
% 10.20/3.74  tff(c_7418, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_5949, c_7389])).
% 10.20/3.74  tff(c_7424, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_7376, c_22])).
% 10.20/3.74  tff(c_7436, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7424, c_38])).
% 10.20/3.74  tff(c_7439, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_7418, c_7436])).
% 10.20/3.74  tff(c_7443, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7439, c_613])).
% 10.20/3.74  tff(c_7468, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5313, c_6156, c_7443])).
% 10.20/3.74  tff(c_7685, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_7591, c_24])).
% 10.20/3.74  tff(c_7692, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_7685, c_14])).
% 10.20/3.74  tff(c_7695, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7484, c_7692])).
% 10.20/3.74  tff(c_7759, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7695, c_12])).
% 10.20/3.74  tff(c_7767, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7484, c_7468, c_7759])).
% 10.20/3.74  tff(c_7686, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_7591, c_22])).
% 10.20/3.74  tff(c_7698, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_7686, c_38])).
% 10.20/3.74  tff(c_7701, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7484, c_7698])).
% 10.20/3.74  tff(c_8234, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7767, c_7701])).
% 10.20/3.74  tff(c_6155, plain, (~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_6011])).
% 10.20/3.74  tff(c_6157, plain, (~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_6155])).
% 10.20/3.74  tff(c_8246, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8234, c_6157])).
% 10.20/3.74  tff(c_8258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8246])).
% 10.20/3.74  tff(c_8259, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_6155])).
% 10.20/3.74  tff(c_8296, plain, (![A_485, B_486]: (m1_subset_1(k2_funct_2(A_485, B_486), k1_zfmisc_1(k2_zfmisc_1(A_485, A_485))) | ~m1_subset_1(B_486, k1_zfmisc_1(k2_zfmisc_1(A_485, A_485))) | ~v3_funct_2(B_486, A_485, A_485) | ~v1_funct_2(B_486, A_485, A_485) | ~v1_funct_1(B_486))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.20/3.74  tff(c_8326, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5312, c_8296])).
% 10.20/3.74  tff(c_8340, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_66, c_8326])).
% 10.20/3.74  tff(c_8353, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_8340, c_30])).
% 10.20/3.74  tff(c_8382, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_5949, c_8353])).
% 10.20/3.74  tff(c_8388, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8340, c_22])).
% 10.20/3.74  tff(c_8400, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_8388, c_38])).
% 10.20/3.74  tff(c_8403, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_8382, c_8400])).
% 10.20/3.74  tff(c_8407, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8403, c_613])).
% 10.20/3.74  tff(c_8432, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5313, c_6156, c_8259, c_8407])).
% 10.20/3.74  tff(c_8260, plain, (r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_6155])).
% 10.20/3.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.20/3.74  tff(c_8272, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_8260, c_2])).
% 10.20/3.74  tff(c_8286, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_8272])).
% 10.20/3.74  tff(c_8448, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8432, c_8286])).
% 10.20/3.74  tff(c_8452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8448])).
% 10.20/3.74  tff(c_8453, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_8272])).
% 10.20/3.74  tff(c_8460, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8453, c_479])).
% 10.20/3.74  tff(c_8482, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5313, c_3988, c_3467, c_8460])).
% 10.20/3.74  tff(c_8691, plain, (![C_494, D_489, A_492, F_493, E_491, B_490]: (k1_partfun1(A_492, B_490, C_494, D_489, E_491, F_493)=k5_relat_1(E_491, F_493) | ~m1_subset_1(F_493, k1_zfmisc_1(k2_zfmisc_1(C_494, D_489))) | ~v1_funct_1(F_493) | ~m1_subset_1(E_491, k1_zfmisc_1(k2_zfmisc_1(A_492, B_490))) | ~v1_funct_1(E_491))), inference(cnfTransformation, [status(thm)], [f_135])).
% 10.20/3.74  tff(c_10180, plain, (![A_525, B_526, A_527, E_528]: (k1_partfun1(A_525, B_526, k1_relat_1(A_527), k2_relat_1(A_527), E_528, A_527)=k5_relat_1(E_528, A_527) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))) | ~v1_funct_1(E_528) | ~v1_funct_1(A_527) | ~v1_relat_1(A_527))), inference(resolution, [status(thm)], [c_58, c_8691])).
% 10.20/3.74  tff(c_10198, plain, (![A_527]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_527), k2_relat_1(A_527), '#skF_2', A_527)=k5_relat_1('#skF_2', A_527) | ~v1_funct_1('#skF_2') | ~v1_funct_1(A_527) | ~v1_relat_1(A_527))), inference(resolution, [status(thm)], [c_66, c_10180])).
% 10.20/3.74  tff(c_10288, plain, (![A_529]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_529), k2_relat_1(A_529), '#skF_2', A_529)=k5_relat_1('#skF_2', A_529) | ~v1_funct_1(A_529) | ~v1_relat_1(A_529))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_10198])).
% 10.20/3.74  tff(c_10312, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', k2_relat_1(k2_funct_1('#skF_2')), '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8453, c_10288])).
% 10.20/3.74  tff(c_10335, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3988, c_5313, c_8482, c_10312])).
% 10.20/3.74  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.20/3.74  tff(c_89, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_64])).
% 10.20/3.74  tff(c_5314, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5312, c_89])).
% 10.20/3.74  tff(c_10656, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10335, c_5314])).
% 10.20/3.74  tff(c_10663, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_10656])).
% 10.20/3.74  tff(c_10666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_72, c_523, c_202, c_3502, c_10663])).
% 10.20/3.74  tff(c_10667, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_64])).
% 10.20/3.74  tff(c_14339, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14336, c_10667])).
% 10.20/3.74  tff(c_15368, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15284, c_14339])).
% 10.20/3.74  tff(c_15426, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74, c_15368])).
% 10.20/3.74  tff(c_15429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10688, c_72, c_11091, c_10781, c_10904, c_15426])).
% 10.20/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.20/3.74  
% 10.20/3.74  Inference rules
% 10.20/3.74  ----------------------
% 10.20/3.74  #Ref     : 0
% 10.20/3.74  #Sup     : 3235
% 10.20/3.74  #Fact    : 0
% 10.20/3.74  #Define  : 0
% 10.20/3.74  #Split   : 59
% 10.20/3.74  #Chain   : 0
% 10.20/3.74  #Close   : 0
% 10.20/3.74  
% 10.20/3.74  Ordering : KBO
% 10.20/3.74  
% 10.20/3.74  Simplification rules
% 10.20/3.74  ----------------------
% 10.20/3.74  #Subsume      : 205
% 10.20/3.74  #Demod        : 7376
% 10.20/3.74  #Tautology    : 1195
% 10.20/3.74  #SimpNegUnit  : 18
% 10.20/3.74  #BackRed      : 329
% 10.20/3.74  
% 10.20/3.74  #Partial instantiations: 0
% 10.20/3.74  #Strategies tried      : 1
% 10.20/3.74  
% 10.20/3.74  Timing (in seconds)
% 10.20/3.74  ----------------------
% 10.20/3.75  Preprocessing        : 0.34
% 10.20/3.75  Parsing              : 0.18
% 10.20/3.75  CNF conversion       : 0.02
% 10.20/3.75  Main loop            : 2.41
% 10.20/3.75  Inferencing          : 0.78
% 10.20/3.75  Reduction            : 0.99
% 10.20/3.75  Demodulation         : 0.74
% 10.20/3.75  BG Simplification    : 0.07
% 10.20/3.75  Subsumption          : 0.39
% 10.20/3.75  Abstraction          : 0.11
% 10.20/3.75  MUC search           : 0.00
% 10.20/3.75  Cooper               : 0.00
% 10.20/3.75  Total                : 2.96
% 10.20/3.75  Index Insertion      : 0.00
% 10.20/3.75  Index Deletion       : 0.00
% 10.20/3.75  Index Matching       : 0.00
% 10.20/3.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
