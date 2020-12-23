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
% DateTime   : Thu Dec  3 10:16:09 EST 2020

% Result     : Theorem 10.12s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :  647 (49972 expanded)
%              Number of leaves         :   46 (17391 expanded)
%              Depth                    :   31
%              Number of atoms          : 1501 (134259 expanded)
%              Number of equality atoms :  247 (12000 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_168,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_145,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_87,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

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

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

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

tff(f_155,axiom,(
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

tff(f_143,axiom,(
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

tff(f_133,axiom,(
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

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_87,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_99,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_93])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_66,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_12352,plain,(
    ! [C_655,A_656,B_657] :
      ( v2_funct_1(C_655)
      | ~ v3_funct_2(C_655,A_656,B_657)
      | ~ v1_funct_1(C_655)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_656,B_657))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12364,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_12352])).

tff(c_12372,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_12364])).

tff(c_54,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_30,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_30])).

tff(c_12248,plain,(
    ! [A_646,B_647,D_648] :
      ( r2_relset_1(A_646,B_647,D_648,D_648)
      | ~ m1_subset_1(D_648,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12253,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_71,c_12248])).

tff(c_11999,plain,(
    ! [C_608,B_609,A_610] :
      ( v5_relat_1(C_608,B_609)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_610,B_609))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12007,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_11999])).

tff(c_12085,plain,(
    ! [B_624,A_625] :
      ( k2_relat_1(B_624) = A_625
      | ~ v2_funct_2(B_624,A_625)
      | ~ v5_relat_1(B_624,A_625)
      | ~ v1_relat_1(B_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12091,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12007,c_12085])).

tff(c_12097,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12091])).

tff(c_12098,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12097])).

tff(c_12209,plain,(
    ! [C_643,B_644,A_645] :
      ( v2_funct_2(C_643,B_644)
      | ~ v3_funct_2(C_643,A_645,B_644)
      | ~ v1_funct_1(C_643)
      | ~ m1_subset_1(C_643,k1_zfmisc_1(k2_zfmisc_1(A_645,B_644))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12218,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_12209])).

tff(c_12223,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_12218])).

tff(c_12225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12098,c_12223])).

tff(c_12226,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12097])).

tff(c_18,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_73,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_partfun1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_68,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12257,plain,(
    ! [A_651] :
      ( m1_subset_1(A_651,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_651),k2_relat_1(A_651))))
      | ~ v1_funct_1(A_651)
      | ~ v1_relat_1(A_651) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_12271,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12226,c_12257])).

tff(c_12282,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_12271])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12295,plain,(
    v4_relat_1('#skF_2',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12282,c_24])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12303,plain,
    ( k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12295,c_14])).

tff(c_12306,plain,(
    k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12303])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12310,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12306,c_12])).

tff(c_12314,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12226,c_12310])).

tff(c_12476,plain,(
    ! [A_669,B_670] :
      ( k9_relat_1(k2_funct_1(A_669),k9_relat_1(A_669,B_670)) = B_670
      | ~ r1_tarski(B_670,k1_relat_1(A_669))
      | ~ v2_funct_1(A_669)
      | ~ v1_funct_1(A_669)
      | ~ v1_relat_1(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12494,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12314,c_12476])).

tff(c_12506,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_12372,c_6,c_12494])).

tff(c_22,plain,(
    ! [C_18,B_17,A_16] :
      ( v5_relat_1(C_18,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12329,plain,(
    ! [A_653] :
      ( v5_relat_1(A_653,k2_relat_1(A_653))
      | ~ v1_funct_1(A_653)
      | ~ v1_relat_1(A_653) ) ),
    inference(resolution,[status(thm)],[c_12257,c_22])).

tff(c_12568,plain,(
    ! [B_676,A_677] :
      ( v5_relat_1(k7_relat_1(B_676,A_677),k9_relat_1(B_676,A_677))
      | ~ v1_funct_1(k7_relat_1(B_676,A_677))
      | ~ v1_relat_1(k7_relat_1(B_676,A_677))
      | ~ v1_relat_1(B_676) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12329])).

tff(c_12577,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12506,c_12568])).

tff(c_12720,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12577])).

tff(c_12722,plain,(
    ! [A_687,B_688] :
      ( k2_funct_2(A_687,B_688) = k2_funct_1(B_688)
      | ~ m1_subset_1(B_688,k1_zfmisc_1(k2_zfmisc_1(A_687,A_687)))
      | ~ v3_funct_2(B_688,A_687,A_687)
      | ~ v1_funct_2(B_688,A_687,A_687)
      | ~ v1_funct_1(B_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12728,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_12722])).

tff(c_12732,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_12728])).

tff(c_12888,plain,(
    ! [A_702,B_703] :
      ( m1_subset_1(k2_funct_2(A_702,B_703),k1_zfmisc_1(k2_zfmisc_1(A_702,A_702)))
      | ~ m1_subset_1(B_703,k1_zfmisc_1(k2_zfmisc_1(A_702,A_702)))
      | ~ v3_funct_2(B_703,A_702,A_702)
      | ~ v1_funct_2(B_703,A_702,A_702)
      | ~ v1_funct_1(B_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12918,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12732,c_12888])).

tff(c_12932,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_12918])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12959,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12932,c_8])).

tff(c_12983,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12959])).

tff(c_12985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12720,c_12983])).

tff(c_12987,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12577])).

tff(c_14969,plain,(
    ! [A_791,B_792] :
      ( k2_funct_2(A_791,B_792) = k2_funct_1(B_792)
      | ~ m1_subset_1(B_792,k1_zfmisc_1(k2_zfmisc_1(A_791,A_791)))
      | ~ v3_funct_2(B_792,A_791,A_791)
      | ~ v1_funct_2(B_792,A_791,A_791)
      | ~ v1_funct_1(B_792) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14975,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_14969])).

tff(c_14979,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_14975])).

tff(c_12708,plain,(
    ! [A_683,B_684] :
      ( v1_funct_1(k2_funct_2(A_683,B_684))
      | ~ m1_subset_1(B_684,k1_zfmisc_1(k2_zfmisc_1(A_683,A_683)))
      | ~ v3_funct_2(B_684,A_683,A_683)
      | ~ v1_funct_2(B_684,A_683,A_683)
      | ~ v1_funct_1(B_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12714,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_12708])).

tff(c_12718,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_12714])).

tff(c_14980,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14979,c_12718])).

tff(c_15182,plain,(
    ! [A_800,B_801] :
      ( v3_funct_2(k2_funct_2(A_800,B_801),A_800,A_800)
      | ~ m1_subset_1(B_801,k1_zfmisc_1(k2_zfmisc_1(A_800,A_800)))
      | ~ v3_funct_2(B_801,A_800,A_800)
      | ~ v1_funct_2(B_801,A_800,A_800)
      | ~ v1_funct_1(B_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15186,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_15182])).

tff(c_15190,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_14979,c_15186])).

tff(c_15465,plain,(
    ! [A_808,B_809] :
      ( m1_subset_1(k2_funct_2(A_808,B_809),k1_zfmisc_1(k2_zfmisc_1(A_808,A_808)))
      | ~ m1_subset_1(B_809,k1_zfmisc_1(k2_zfmisc_1(A_808,A_808)))
      | ~ v3_funct_2(B_809,A_808,A_808)
      | ~ v1_funct_2(B_809,A_808,A_808)
      | ~ v1_funct_1(B_809) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15495,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14979,c_15465])).

tff(c_15509,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_15495])).

tff(c_32,plain,(
    ! [C_26,B_25,A_24] :
      ( v2_funct_2(C_26,B_25)
      | ~ v3_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_15522,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_15509,c_32])).

tff(c_15551,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14980,c_15190,c_15522])).

tff(c_15557,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_15509,c_22])).

tff(c_40,plain,(
    ! [B_28,A_27] :
      ( k2_relat_1(B_28) = A_27
      | ~ v2_funct_2(B_28,A_27)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_15569,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_15557,c_40])).

tff(c_15572,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12987,c_15551,c_15569])).

tff(c_15556,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_15509,c_24])).

tff(c_15563,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_15556,c_14])).

tff(c_15566,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12987,c_15563])).

tff(c_14169,plain,(
    ! [A_758,B_759] :
      ( k2_funct_2(A_758,B_759) = k2_funct_1(B_759)
      | ~ m1_subset_1(B_759,k1_zfmisc_1(k2_zfmisc_1(A_758,A_758)))
      | ~ v3_funct_2(B_759,A_758,A_758)
      | ~ v1_funct_2(B_759,A_758,A_758)
      | ~ v1_funct_1(B_759) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14175,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_14169])).

tff(c_14179,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_14175])).

tff(c_14804,plain,(
    ! [A_789,B_790] :
      ( m1_subset_1(k2_funct_2(A_789,B_790),k1_zfmisc_1(k2_zfmisc_1(A_789,A_789)))
      | ~ m1_subset_1(B_790,k1_zfmisc_1(k2_zfmisc_1(A_789,A_789)))
      | ~ v3_funct_2(B_790,A_789,A_789)
      | ~ v1_funct_2(B_790,A_789,A_789)
      | ~ v1_funct_1(B_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14834,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14179,c_14804])).

tff(c_14848,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_14834])).

tff(c_14895,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14848,c_24])).

tff(c_14902,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14895,c_14])).

tff(c_14905,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12987,c_14902])).

tff(c_13587,plain,(
    ! [A_730,B_731] :
      ( k2_funct_2(A_730,B_731) = k2_funct_1(B_731)
      | ~ m1_subset_1(B_731,k1_zfmisc_1(k2_zfmisc_1(A_730,A_730)))
      | ~ v3_funct_2(B_731,A_730,A_730)
      | ~ v1_funct_2(B_731,A_730,A_730)
      | ~ v1_funct_1(B_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_13593,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_13587])).

tff(c_13597,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_13593])).

tff(c_13598,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13597,c_12718])).

tff(c_14008,plain,(
    ! [A_756,B_757] :
      ( m1_subset_1(k2_funct_2(A_756,B_757),k1_zfmisc_1(k2_zfmisc_1(A_756,A_756)))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(k2_zfmisc_1(A_756,A_756)))
      | ~ v3_funct_2(B_757,A_756,A_756)
      | ~ v1_funct_2(B_757,A_756,A_756)
      | ~ v1_funct_1(B_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14038,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13597,c_14008])).

tff(c_14052,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_14038])).

tff(c_14099,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14052,c_24])).

tff(c_14106,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14099,c_14])).

tff(c_14109,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12987,c_14106])).

tff(c_12986,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12577])).

tff(c_12988,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_12986])).

tff(c_14161,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14109,c_12988])).

tff(c_14165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13598,c_14161])).

tff(c_14166,plain,
    ( ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12986])).

tff(c_14168,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_14166])).

tff(c_14956,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14905,c_14168])).

tff(c_14960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12987,c_14956])).

tff(c_14962,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14166])).

tff(c_14961,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14166])).

tff(c_14965,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2')
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_14961,c_40])).

tff(c_14968,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2')
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14962,c_14965])).

tff(c_14993,plain,(
    ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14968])).

tff(c_14167,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_12986])).

tff(c_38,plain,(
    ! [B_28] :
      ( v2_funct_2(B_28,k2_relat_1(B_28))
      | ~ v5_relat_1(B_28,k2_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12374,plain,(
    ! [A_658] :
      ( v2_funct_2(A_658,k2_relat_1(A_658))
      | ~ v1_funct_1(A_658)
      | ~ v1_relat_1(A_658) ) ),
    inference(resolution,[status(thm)],[c_12329,c_38])).

tff(c_12634,plain,(
    ! [B_680,A_681] :
      ( v2_funct_2(k7_relat_1(B_680,A_681),k9_relat_1(B_680,A_681))
      | ~ v1_funct_1(k7_relat_1(B_680,A_681))
      | ~ v1_relat_1(k7_relat_1(B_680,A_681))
      | ~ v1_relat_1(B_680) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12374])).

tff(c_12640,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12506,c_12634])).

tff(c_15007,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12987,c_14962,c_14167,c_12640])).

tff(c_15008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14993,c_15007])).

tff(c_15009,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = k1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_14968])).

tff(c_15626,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15566,c_15009])).

tff(c_15631,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15572,c_15626])).

tff(c_12009,plain,(
    ! [C_612,A_613,B_614] :
      ( v4_relat_1(C_612,A_613)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(k2_zfmisc_1(A_613,B_614))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12017,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_12009])).

tff(c_12028,plain,(
    ! [B_618,A_619] :
      ( k7_relat_1(B_618,A_619) = B_618
      | ~ v4_relat_1(B_618,A_619)
      | ~ v1_relat_1(B_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12034,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12017,c_12028])).

tff(c_12040,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12034])).

tff(c_12044,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12040,c_12])).

tff(c_12048,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_12044])).

tff(c_12228,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12226,c_12048])).

tff(c_12497,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12228,c_12476])).

tff(c_12508,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_12372,c_12497])).

tff(c_12518,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12506,c_12508])).

tff(c_12519,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12518])).

tff(c_15653,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15631,c_12519])).

tff(c_15663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15653])).

tff(c_15664,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12518])).

tff(c_16,plain,(
    ! [A_12,B_14] :
      ( k9_relat_1(k2_funct_1(A_12),k9_relat_1(A_12,B_14)) = B_14
      | ~ r1_tarski(B_14,k1_relat_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12514,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12506,c_16])).

tff(c_15872,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15664,c_12514])).

tff(c_15873,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_15872])).

tff(c_15903,plain,(
    ! [A_826,B_827] :
      ( k2_funct_2(A_826,B_827) = k2_funct_1(B_827)
      | ~ m1_subset_1(B_827,k1_zfmisc_1(k2_zfmisc_1(A_826,A_826)))
      | ~ v3_funct_2(B_827,A_826,A_826)
      | ~ v1_funct_2(B_827,A_826,A_826)
      | ~ v1_funct_1(B_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_15909,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_15903])).

tff(c_15913,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_15909])).

tff(c_16088,plain,(
    ! [A_843,B_844] :
      ( m1_subset_1(k2_funct_2(A_843,B_844),k1_zfmisc_1(k2_zfmisc_1(A_843,A_843)))
      | ~ m1_subset_1(B_844,k1_zfmisc_1(k2_zfmisc_1(A_843,A_843)))
      | ~ v3_funct_2(B_844,A_843,A_843)
      | ~ v1_funct_2(B_844,A_843,A_843)
      | ~ v1_funct_1(B_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16118,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15913,c_16088])).

tff(c_16132,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_16118])).

tff(c_16159,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16132,c_8])).

tff(c_16183,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16159])).

tff(c_16185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15873,c_16183])).

tff(c_16187,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_15872])).

tff(c_18572,plain,(
    ! [A_957,B_958] :
      ( k2_funct_2(A_957,B_958) = k2_funct_1(B_958)
      | ~ m1_subset_1(B_958,k1_zfmisc_1(k2_zfmisc_1(A_957,A_957)))
      | ~ v3_funct_2(B_958,A_957,A_957)
      | ~ v1_funct_2(B_958,A_957,A_957)
      | ~ v1_funct_1(B_958) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_18578,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_18572])).

tff(c_18582,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_18578])).

tff(c_15824,plain,(
    ! [A_819,B_820] :
      ( v1_funct_1(k2_funct_2(A_819,B_820))
      | ~ m1_subset_1(B_820,k1_zfmisc_1(k2_zfmisc_1(A_819,A_819)))
      | ~ v3_funct_2(B_820,A_819,A_819)
      | ~ v1_funct_2(B_820,A_819,A_819)
      | ~ v1_funct_1(B_820) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_15830,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_15824])).

tff(c_15834,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_15830])).

tff(c_18583,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18582,c_15834])).

tff(c_16217,plain,(
    ! [A_846,B_847] :
      ( k2_funct_2(A_846,B_847) = k2_funct_1(B_847)
      | ~ m1_subset_1(B_847,k1_zfmisc_1(k2_zfmisc_1(A_846,A_846)))
      | ~ v3_funct_2(B_847,A_846,A_846)
      | ~ v1_funct_2(B_847,A_846,A_846)
      | ~ v1_funct_1(B_847) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_16223,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_16217])).

tff(c_16227,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_16223])).

tff(c_16228,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16227,c_15834])).

tff(c_16769,plain,(
    ! [A_881,B_882] :
      ( v1_funct_2(k2_funct_2(A_881,B_882),A_881,A_881)
      | ~ m1_subset_1(B_882,k1_zfmisc_1(k2_zfmisc_1(A_881,A_881)))
      | ~ v3_funct_2(B_882,A_881,A_881)
      | ~ v1_funct_2(B_882,A_881,A_881)
      | ~ v1_funct_1(B_882) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16773,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_16769])).

tff(c_16777,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_16227,c_16773])).

tff(c_16909,plain,(
    ! [A_883,B_884] :
      ( v3_funct_2(k2_funct_2(A_883,B_884),A_883,A_883)
      | ~ m1_subset_1(B_884,k1_zfmisc_1(k2_zfmisc_1(A_883,A_883)))
      | ~ v3_funct_2(B_884,A_883,A_883)
      | ~ v1_funct_2(B_884,A_883,A_883)
      | ~ v1_funct_1(B_884) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16913,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_16909])).

tff(c_16917,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_16227,c_16913])).

tff(c_17419,plain,(
    ! [A_899,B_900] :
      ( m1_subset_1(k2_funct_2(A_899,B_900),k1_zfmisc_1(k2_zfmisc_1(A_899,A_899)))
      | ~ m1_subset_1(B_900,k1_zfmisc_1(k2_zfmisc_1(A_899,A_899)))
      | ~ v3_funct_2(B_900,A_899,A_899)
      | ~ v1_funct_2(B_900,A_899,A_899)
      | ~ v1_funct_1(B_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_17449,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16227,c_17419])).

tff(c_17463,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_17449])).

tff(c_52,plain,(
    ! [A_37,B_38] :
      ( k2_funct_2(A_37,B_38) = k2_funct_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k2_zfmisc_1(A_37,A_37)))
      | ~ v3_funct_2(B_38,A_37,A_37)
      | ~ v1_funct_2(B_38,A_37,A_37)
      | ~ v1_funct_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_17470,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_17463,c_52])).

tff(c_17499,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16777,c_16917,c_17470])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_funct_2(A_29,B_30),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_17670,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17499,c_42])).

tff(c_17674,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16777,c_16917,c_17463,c_17670])).

tff(c_17743,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_17674,c_8])).

tff(c_17773,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_17743])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( v1_funct_1(k2_funct_2(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_17473,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_17463,c_48])).

tff(c_17502,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16777,c_16917,c_17473])).

tff(c_17666,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17499,c_17502])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( v3_funct_2(k2_funct_2(A_29,B_30),A_29,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_17465,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_17463,c_44])).

tff(c_17493,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16777,c_16917,c_17465])).

tff(c_17665,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17499,c_17493])).

tff(c_17729,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_17674,c_32])).

tff(c_17764,plain,(
    v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17666,c_17665,c_17729])).

tff(c_17770,plain,(
    v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17674,c_22])).

tff(c_17783,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_17770,c_40])).

tff(c_17786,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17773,c_17764,c_17783])).

tff(c_17769,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17674,c_24])).

tff(c_17776,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_17769,c_14])).

tff(c_17779,plain,(
    k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17773,c_17776])).

tff(c_17841,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17779,c_12])).

tff(c_17849,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17773,c_17786,c_17841])).

tff(c_34,plain,(
    ! [C_26,A_24,B_25] :
      ( v2_funct_1(C_26)
      | ~ v3_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_17479,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_17463,c_34])).

tff(c_17508,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16917,c_17479])).

tff(c_17510,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17463,c_24])).

tff(c_17517,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_17510,c_14])).

tff(c_17520,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_17517])).

tff(c_16365,plain,(
    ! [A_861,B_862] :
      ( m1_subset_1(k2_funct_2(A_861,B_862),k1_zfmisc_1(k2_zfmisc_1(A_861,A_861)))
      | ~ m1_subset_1(B_862,k1_zfmisc_1(k2_zfmisc_1(A_861,A_861)))
      | ~ v3_funct_2(B_862,A_861,A_861)
      | ~ v1_funct_2(B_862,A_861,A_861)
      | ~ v1_funct_1(B_862) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16395,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16227,c_16365])).

tff(c_16409,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_16395])).

tff(c_16456,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16409,c_24])).

tff(c_16463,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16456,c_14])).

tff(c_16466,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_16463])).

tff(c_15666,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15664,c_12506])).

tff(c_15835,plain,(
    ! [B_821,A_822] :
      ( v2_funct_2(k7_relat_1(B_821,A_822),k9_relat_1(B_821,A_822))
      | ~ v1_funct_1(k7_relat_1(B_821,A_822))
      | ~ v1_relat_1(k7_relat_1(B_821,A_822))
      | ~ v1_relat_1(B_821) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12374])).

tff(c_15841,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15666,c_15835])).

tff(c_16243,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_15841])).

tff(c_16244,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16243])).

tff(c_16537,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16466,c_16244])).

tff(c_16540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_16537])).

tff(c_16542,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16243])).

tff(c_16610,plain,(
    ! [A_879,B_880] :
      ( m1_subset_1(k2_funct_2(A_879,B_880),k1_zfmisc_1(k2_zfmisc_1(A_879,A_879)))
      | ~ m1_subset_1(B_880,k1_zfmisc_1(k2_zfmisc_1(A_879,A_879)))
      | ~ v3_funct_2(B_880,A_879,A_879)
      | ~ v1_funct_2(B_880,A_879,A_879)
      | ~ v1_funct_1(B_880) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16640,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16227,c_16610])).

tff(c_16654,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_16640])).

tff(c_16701,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_16654,c_24])).

tff(c_16708,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16701,c_14])).

tff(c_16711,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_16708])).

tff(c_16541,plain,
    ( ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_16243])).

tff(c_16543,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16541])).

tff(c_16762,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16711,c_16543])).

tff(c_16766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16228,c_16762])).

tff(c_16767,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_16541])).

tff(c_16768,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16541])).

tff(c_15769,plain,(
    ! [B_815,A_816] :
      ( v5_relat_1(k7_relat_1(B_815,A_816),k9_relat_1(B_815,A_816))
      | ~ v1_funct_1(k7_relat_1(B_815,A_816))
      | ~ v1_relat_1(k7_relat_1(B_815,A_816))
      | ~ v1_relat_1(B_815) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12329])).

tff(c_15778,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15666,c_15769])).

tff(c_16779,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_16542,c_16768,c_15778])).

tff(c_16782,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_16779,c_40])).

tff(c_16785,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16542,c_16767,c_16782])).

tff(c_17534,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17520,c_16785])).

tff(c_12347,plain,(
    ! [A_654] :
      ( v4_relat_1(A_654,k1_relat_1(A_654))
      | ~ v1_funct_1(A_654)
      | ~ v1_relat_1(A_654) ) ),
    inference(resolution,[status(thm)],[c_12257,c_24])).

tff(c_12383,plain,(
    ! [A_659] :
      ( k7_relat_1(A_659,k1_relat_1(A_659)) = A_659
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(resolution,[status(thm)],[c_12347,c_14])).

tff(c_12392,plain,(
    ! [A_659] :
      ( k9_relat_1(A_659,k1_relat_1(A_659)) = k2_relat_1(A_659)
      | ~ v1_relat_1(A_659)
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12383,c_12])).

tff(c_12491,plain,(
    ! [A_659] :
      ( k9_relat_1(k2_funct_1(A_659),k2_relat_1(A_659)) = k1_relat_1(A_659)
      | ~ r1_tarski(k1_relat_1(A_659),k1_relat_1(A_659))
      | ~ v2_funct_1(A_659)
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659)
      | ~ v1_relat_1(A_659)
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12392,c_12476])).

tff(c_12504,plain,(
    ! [A_659] :
      ( k9_relat_1(k2_funct_1(A_659),k2_relat_1(A_659)) = k1_relat_1(A_659)
      | ~ v2_funct_1(A_659)
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12491])).

tff(c_17566,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17534,c_12504])).

tff(c_17591,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_16228,c_17508,c_17566])).

tff(c_17899,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17849,c_17591])).

tff(c_16186,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15872])).

tff(c_16188,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_16186])).

tff(c_17903,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17899,c_16188])).

tff(c_17909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17903])).

tff(c_17910,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16186])).

tff(c_18593,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_2'))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18583,c_17910])).

tff(c_18594,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18593])).

tff(c_18642,plain,(
    ! [A_965,B_966] :
      ( v3_funct_2(k2_funct_2(A_965,B_966),A_965,A_965)
      | ~ m1_subset_1(B_966,k1_zfmisc_1(k2_zfmisc_1(A_965,A_965)))
      | ~ v3_funct_2(B_966,A_965,A_965)
      | ~ v1_funct_2(B_966,A_965,A_965)
      | ~ v1_funct_1(B_966) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18646,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_18642])).

tff(c_18650,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_18582,c_18646])).

tff(c_18654,plain,(
    ! [A_968,B_969] :
      ( m1_subset_1(k2_funct_2(A_968,B_969),k1_zfmisc_1(k2_zfmisc_1(A_968,A_968)))
      | ~ m1_subset_1(B_969,k1_zfmisc_1(k2_zfmisc_1(A_968,A_968)))
      | ~ v3_funct_2(B_969,A_968,A_968)
      | ~ v1_funct_2(B_969,A_968,A_968)
      | ~ v1_funct_1(B_969) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18684,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18582,c_18654])).

tff(c_18698,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_18684])).

tff(c_18714,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18698,c_34])).

tff(c_18743,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18583,c_18650,c_18714])).

tff(c_18745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18594,c_18743])).

tff(c_18747,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18593])).

tff(c_18746,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18593])).

tff(c_18810,plain,(
    ! [A_976,B_977] :
      ( v3_funct_2(k2_funct_2(A_976,B_977),A_976,A_976)
      | ~ m1_subset_1(B_977,k1_zfmisc_1(k2_zfmisc_1(A_976,A_976)))
      | ~ v3_funct_2(B_977,A_976,A_976)
      | ~ v1_funct_2(B_977,A_976,A_976)
      | ~ v1_funct_1(B_977) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18814,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_18810])).

tff(c_18818,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_18582,c_18814])).

tff(c_18909,plain,(
    ! [A_984,B_985] :
      ( m1_subset_1(k2_funct_2(A_984,B_985),k1_zfmisc_1(k2_zfmisc_1(A_984,A_984)))
      | ~ m1_subset_1(B_985,k1_zfmisc_1(k2_zfmisc_1(A_984,A_984)))
      | ~ v3_funct_2(B_985,A_984,A_984)
      | ~ v1_funct_2(B_985,A_984,A_984)
      | ~ v1_funct_1(B_985) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18939,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18582,c_18909])).

tff(c_18953,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_18939])).

tff(c_18966,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18953,c_32])).

tff(c_18995,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18583,c_18818,c_18966])).

tff(c_19001,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18953,c_22])).

tff(c_19013,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_19001,c_40])).

tff(c_19016,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_18995,c_19013])).

tff(c_19020,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19016,c_12504])).

tff(c_19045,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_18583,c_18747,c_18746,c_19020])).

tff(c_17911,plain,(
    r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_16186])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17914,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17911,c_2])).

tff(c_18571,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_17914])).

tff(c_19061,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19045,c_18571])).

tff(c_19065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19061])).

tff(c_19066,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17914])).

tff(c_12276,plain,(
    ! [A_651] :
      ( v4_relat_1(A_651,k1_relat_1(A_651))
      | ~ v1_funct_1(A_651)
      | ~ v1_relat_1(A_651) ) ),
    inference(resolution,[status(thm)],[c_12257,c_24])).

tff(c_19085,plain,
    ( v4_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19066,c_12276])).

tff(c_19103,plain,
    ( v4_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16187,c_19085])).

tff(c_19110,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_19103])).

tff(c_19111,plain,(
    ! [A_986,B_987] :
      ( k2_funct_2(A_986,B_987) = k2_funct_1(B_987)
      | ~ m1_subset_1(B_987,k1_zfmisc_1(k2_zfmisc_1(A_986,A_986)))
      | ~ v3_funct_2(B_987,A_986,A_986)
      | ~ v1_funct_2(B_987,A_986,A_986)
      | ~ v1_funct_1(B_987) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_19117,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_19111])).

tff(c_19121,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_19117])).

tff(c_19122,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19121,c_15834])).

tff(c_19127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19110,c_19122])).

tff(c_19129,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_19103])).

tff(c_19152,plain,(
    ! [A_988,B_989] :
      ( k2_funct_2(A_988,B_989) = k2_funct_1(B_989)
      | ~ m1_subset_1(B_989,k1_zfmisc_1(k2_zfmisc_1(A_988,A_988)))
      | ~ v3_funct_2(B_989,A_988,A_988)
      | ~ v1_funct_2(B_989,A_988,A_988)
      | ~ v1_funct_1(B_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_19158,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_19152])).

tff(c_19162,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_19158])).

tff(c_19509,plain,(
    ! [F_1002,D_998,E_1000,B_999,A_1001,C_1003] :
      ( k1_partfun1(A_1001,B_999,C_1003,D_998,E_1000,F_1002) = k5_relat_1(E_1000,F_1002)
      | ~ m1_subset_1(F_1002,k1_zfmisc_1(k2_zfmisc_1(C_1003,D_998)))
      | ~ v1_funct_1(F_1002)
      | ~ m1_subset_1(E_1000,k1_zfmisc_1(k2_zfmisc_1(A_1001,B_999)))
      | ~ v1_funct_1(E_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_19521,plain,(
    ! [A_1001,B_999,E_1000] :
      ( k1_partfun1(A_1001,B_999,'#skF_1','#skF_1',E_1000,'#skF_2') = k5_relat_1(E_1000,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1000,k1_zfmisc_1(k2_zfmisc_1(A_1001,B_999)))
      | ~ v1_funct_1(E_1000) ) ),
    inference(resolution,[status(thm)],[c_64,c_19509])).

tff(c_19553,plain,(
    ! [A_1004,B_1005,E_1006] :
      ( k1_partfun1(A_1004,B_1005,'#skF_1','#skF_1',E_1006,'#skF_2') = k5_relat_1(E_1006,'#skF_2')
      | ~ m1_subset_1(E_1006,k1_zfmisc_1(k2_zfmisc_1(A_1004,B_1005)))
      | ~ v1_funct_1(E_1006) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_19521])).

tff(c_19981,plain,(
    ! [A_1014,B_1015] :
      ( k1_partfun1(A_1014,A_1014,'#skF_1','#skF_1',k2_funct_2(A_1014,B_1015),'#skF_2') = k5_relat_1(k2_funct_2(A_1014,B_1015),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1014,B_1015))
      | ~ m1_subset_1(B_1015,k1_zfmisc_1(k2_zfmisc_1(A_1014,A_1014)))
      | ~ v3_funct_2(B_1015,A_1014,A_1014)
      | ~ v1_funct_2(B_1015,A_1014,A_1014)
      | ~ v1_funct_1(B_1015) ) ),
    inference(resolution,[status(thm)],[c_42,c_19553])).

tff(c_19995,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_19981])).

tff(c_20012,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_19129,c_19162,c_19162,c_19162,c_19995])).

tff(c_500,plain,(
    ! [C_102,A_103,B_104] :
      ( v2_funct_1(C_102)
      | ~ v3_funct_2(C_102,A_103,B_104)
      | ~ v1_funct_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_512,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_500])).

tff(c_520,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_512])).

tff(c_364,plain,(
    ! [A_92,B_93,D_94] :
      ( r2_relset_1(A_92,B_93,D_94,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_369,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_71,c_364])).

tff(c_177,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_177])).

tff(c_195,plain,(
    ! [B_67,A_68] :
      ( k2_relat_1(B_67) = A_68
      | ~ v2_funct_2(B_67,A_68)
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_201,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_185,c_195])).

tff(c_207,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_201])).

tff(c_208,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_324,plain,(
    ! [C_88,B_89,A_90] :
      ( v2_funct_2(C_88,B_89)
      | ~ v3_funct_2(C_88,A_90,B_89)
      | ~ v1_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_333,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_324])).

tff(c_338,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_333])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_338])).

tff(c_341,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_372,plain,(
    ! [A_96] :
      ( m1_subset_1(A_96,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96),k2_relat_1(A_96))))
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_386,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_372])).

tff(c_397,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_386])).

tff(c_412,plain,(
    v4_relat_1('#skF_2',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_397,c_24])).

tff(c_418,plain,
    ( k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_412,c_14])).

tff(c_421,plain,(
    k7_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_418])).

tff(c_425,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_12])).

tff(c_429,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_341,c_425])).

tff(c_591,plain,(
    ! [A_114,B_115] :
      ( k9_relat_1(k2_funct_1(A_114),k9_relat_1(A_114,B_115)) = B_115
      | ~ r1_tarski(B_115,k1_relat_1(A_114))
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_609,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_591])).

tff(c_621,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_520,c_6,c_609])).

tff(c_435,plain,(
    ! [A_97] :
      ( v5_relat_1(A_97,k2_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_372,c_22])).

tff(c_655,plain,(
    ! [B_117,A_118] :
      ( v5_relat_1(k7_relat_1(B_117,A_118),k9_relat_1(B_117,A_118))
      | ~ v1_funct_1(k7_relat_1(B_117,A_118))
      | ~ v1_relat_1(k7_relat_1(B_117,A_118))
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_435])).

tff(c_664,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_655])).

tff(c_743,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_831,plain,(
    ! [A_132,B_133] :
      ( k2_funct_2(A_132,B_133) = k2_funct_1(B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_132,A_132)))
      | ~ v3_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_837,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_831])).

tff(c_841,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_837])).

tff(c_989,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1(k2_funct_2(A_146,B_147),k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ v3_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1019,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_989])).

tff(c_1033,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_1019])).

tff(c_1060,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1033,c_8])).

tff(c_1084,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1060])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_743,c_1084])).

tff(c_1088,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_629,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_16])).

tff(c_1090,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_629])).

tff(c_1091,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_1181,plain,(
    ! [A_154,B_155] :
      ( k2_funct_2(A_154,B_155) = k2_funct_1(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_zfmisc_1(A_154,A_154)))
      | ~ v3_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_2(B_155,A_154,A_154)
      | ~ v1_funct_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1187,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1181])).

tff(c_1191,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1187])).

tff(c_1141,plain,(
    ! [A_150,B_151] :
      ( v1_funct_1(k2_funct_2(A_150,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_zfmisc_1(A_150,A_150)))
      | ~ v3_funct_2(B_151,A_150,A_150)
      | ~ v1_funct_2(B_151,A_150,A_150)
      | ~ v1_funct_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1147,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1141])).

tff(c_1151,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1147])).

tff(c_1192,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_1151])).

tff(c_1195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1091,c_1192])).

tff(c_1197,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_1746,plain,(
    ! [A_193,B_194] :
      ( k2_funct_2(A_193,B_194) = k2_funct_1(B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1752,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1746])).

tff(c_1756,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1752])).

tff(c_1936,plain,(
    ! [A_197,B_198] :
      ( v3_funct_2(k2_funct_2(A_197,B_198),A_197,A_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_zfmisc_1(A_197,A_197)))
      | ~ v3_funct_2(B_198,A_197,A_197)
      | ~ v1_funct_2(B_198,A_197,A_197)
      | ~ v1_funct_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1940,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1936])).

tff(c_1944,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1756,c_1940])).

tff(c_2094,plain,(
    ! [A_202,B_203] :
      ( m1_subset_1(k2_funct_2(A_202,B_203),k1_zfmisc_1(k2_zfmisc_1(A_202,A_202)))
      | ~ m1_subset_1(B_203,k1_zfmisc_1(k2_zfmisc_1(A_202,A_202)))
      | ~ v3_funct_2(B_203,A_202,A_202)
      | ~ v1_funct_2(B_203,A_202,A_202)
      | ~ v1_funct_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2124,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_2094])).

tff(c_2138,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_2124])).

tff(c_2151,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2138,c_32])).

tff(c_2180,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1944,c_2151])).

tff(c_2186,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2138,c_24])).

tff(c_2198,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2186,c_14])).

tff(c_2201,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_2198])).

tff(c_2228,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2201,c_12])).

tff(c_2236,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_621,c_2228])).

tff(c_2185,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2138,c_22])).

tff(c_2192,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2185,c_40])).

tff(c_2195,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_2192])).

tff(c_2400,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_2236,c_2195])).

tff(c_109,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_117,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_109])).

tff(c_118,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_121,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_118])).

tff(c_124,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_121])).

tff(c_145,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k7_relat_1(B_58,A_59)) = k9_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_157,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_145])).

tff(c_163,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_157])).

tff(c_343,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_163])).

tff(c_612,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_591])).

tff(c_623,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_520,c_612])).

tff(c_633,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_623])).

tff(c_634,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_2404,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_634])).

tff(c_2416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2404])).

tff(c_2417,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_633])).

tff(c_20,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_partfun1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20])).

tff(c_2502,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_629])).

tff(c_2503,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2502])).

tff(c_2656,plain,(
    ! [A_231,B_232] :
      ( k2_funct_2(A_231,B_232) = k2_funct_1(B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k2_zfmisc_1(A_231,A_231)))
      | ~ v3_funct_2(B_232,A_231,A_231)
      | ~ v1_funct_2(B_232,A_231,A_231)
      | ~ v1_funct_1(B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2662,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2656])).

tff(c_2666,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2662])).

tff(c_2748,plain,(
    ! [A_243,B_244] :
      ( m1_subset_1(k2_funct_2(A_243,B_244),k1_zfmisc_1(k2_zfmisc_1(A_243,A_243)))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(k2_zfmisc_1(A_243,A_243)))
      | ~ v3_funct_2(B_244,A_243,A_243)
      | ~ v1_funct_2(B_244,A_243,A_243)
      | ~ v1_funct_1(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2778,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2666,c_2748])).

tff(c_2792,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_2778])).

tff(c_2819,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_2792,c_8])).

tff(c_2843,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2819])).

tff(c_2845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2503,c_2843])).

tff(c_2847,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2502])).

tff(c_2442,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_621])).

tff(c_2498,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_16])).

tff(c_2937,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2498])).

tff(c_2938,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2937])).

tff(c_2978,plain,(
    ! [A_254,B_255] :
      ( k2_funct_2(A_254,B_255) = k2_funct_1(B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_zfmisc_1(A_254,A_254)))
      | ~ v3_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2984,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2978])).

tff(c_2988,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2984])).

tff(c_2924,plain,(
    ! [A_249,B_250] :
      ( v1_funct_1(k2_funct_2(A_249,B_250))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(k2_zfmisc_1(A_249,A_249)))
      | ~ v3_funct_2(B_250,A_249,A_249)
      | ~ v1_funct_2(B_250,A_249,A_249)
      | ~ v1_funct_1(B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2930,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2924])).

tff(c_2934,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_2930])).

tff(c_2989,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2988,c_2934])).

tff(c_2992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2938,c_2989])).

tff(c_2994,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2937])).

tff(c_3611,plain,(
    ! [A_304,B_305] :
      ( k2_funct_2(A_304,B_305) = k2_funct_1(B_305)
      | ~ m1_subset_1(B_305,k1_zfmisc_1(k2_zfmisc_1(A_304,A_304)))
      | ~ v3_funct_2(B_305,A_304,A_304)
      | ~ v1_funct_2(B_305,A_304,A_304)
      | ~ v1_funct_1(B_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3617,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3611])).

tff(c_3621,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3617])).

tff(c_6655,plain,(
    ! [A_418,B_419] :
      ( v1_funct_2(k2_funct_2(A_418,B_419),A_418,A_418)
      | ~ m1_subset_1(B_419,k1_zfmisc_1(k2_zfmisc_1(A_418,A_418)))
      | ~ v3_funct_2(B_419,A_418,A_418)
      | ~ v1_funct_2(B_419,A_418,A_418)
      | ~ v1_funct_1(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6659,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_6655])).

tff(c_6663,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3621,c_6659])).

tff(c_3717,plain,(
    ! [A_306,B_307] :
      ( v3_funct_2(k2_funct_2(A_306,B_307),A_306,A_306)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(k2_zfmisc_1(A_306,A_306)))
      | ~ v3_funct_2(B_307,A_306,A_306)
      | ~ v1_funct_2(B_307,A_306,A_306)
      | ~ v1_funct_1(B_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3721,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3717])).

tff(c_3725,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3621,c_3721])).

tff(c_6760,plain,(
    ! [A_425,B_426] :
      ( m1_subset_1(k2_funct_2(A_425,B_426),k1_zfmisc_1(k2_zfmisc_1(A_425,A_425)))
      | ~ m1_subset_1(B_426,k1_zfmisc_1(k2_zfmisc_1(A_425,A_425)))
      | ~ v3_funct_2(B_426,A_425,A_425)
      | ~ v1_funct_2(B_426,A_425,A_425)
      | ~ v1_funct_1(B_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6790,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_6760])).

tff(c_6804,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_6790])).

tff(c_6811,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6804,c_52])).

tff(c_6840,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_6663,c_3725,c_6811])).

tff(c_6814,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6804,c_48])).

tff(c_6843,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_6663,c_3725,c_6814])).

tff(c_7009,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6840,c_6843])).

tff(c_6808,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6804,c_44])).

tff(c_6837,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_6663,c_3725,c_6808])).

tff(c_7019,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6840,c_6837])).

tff(c_7013,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6840,c_42])).

tff(c_7017,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_6663,c_3725,c_6804,c_7013])).

tff(c_7074,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7017,c_32])).

tff(c_7109,plain,(
    v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7009,c_7019,c_7074])).

tff(c_7088,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_7017,c_8])).

tff(c_7118,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7088])).

tff(c_6820,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6804,c_34])).

tff(c_6849,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_3725,c_6820])).

tff(c_6852,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6804,c_24])).

tff(c_6864,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6852,c_14])).

tff(c_6867,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_6864])).

tff(c_3038,plain,(
    ! [A_259,B_260] :
      ( k2_funct_2(A_259,B_260) = k2_funct_1(B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3044,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3038])).

tff(c_3048,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3044])).

tff(c_3136,plain,(
    ! [A_272,B_273] :
      ( m1_subset_1(k2_funct_2(A_272,B_273),k1_zfmisc_1(k2_zfmisc_1(A_272,A_272)))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(k2_zfmisc_1(A_272,A_272)))
      | ~ v3_funct_2(B_273,A_272,A_272)
      | ~ v1_funct_2(B_273,A_272,A_272)
      | ~ v1_funct_1(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3166,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_3136])).

tff(c_3180,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_3166])).

tff(c_3228,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3180,c_24])).

tff(c_3240,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3228,c_14])).

tff(c_3243,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_3240])).

tff(c_2868,plain,(
    ! [B_246,A_247] :
      ( v5_relat_1(k7_relat_1(B_246,A_247),k9_relat_1(B_246,A_247))
      | ~ v1_funct_1(k7_relat_1(B_246,A_247))
      | ~ v1_relat_1(k7_relat_1(B_246,A_247))
      | ~ v1_relat_1(B_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_435])).

tff(c_2877,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_2868])).

tff(c_2901,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2877])).

tff(c_2996,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2901])).

tff(c_3264,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3243,c_2996])).

tff(c_3267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_3264])).

tff(c_3269,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2901])).

tff(c_3312,plain,(
    ! [A_282,B_283] :
      ( k2_funct_2(A_282,B_283) = k2_funct_1(B_283)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(k2_zfmisc_1(A_282,A_282)))
      | ~ v3_funct_2(B_283,A_282,A_282)
      | ~ v1_funct_2(B_283,A_282,A_282)
      | ~ v1_funct_1(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3318,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_3312])).

tff(c_3322,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_3318])).

tff(c_3381,plain,(
    ! [A_294,B_295] :
      ( m1_subset_1(k2_funct_2(A_294,B_295),k1_zfmisc_1(k2_zfmisc_1(A_294,A_294)))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(k2_zfmisc_1(A_294,A_294)))
      | ~ v3_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_1(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3411,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3322,c_3381])).

tff(c_3425,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_3411])).

tff(c_3473,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3425,c_24])).

tff(c_3485,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3473,c_14])).

tff(c_3488,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_3485])).

tff(c_3268,plain,
    ( ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2901])).

tff(c_3273,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3268])).

tff(c_3509,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3488,c_3273])).

tff(c_3513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_3509])).

tff(c_3514,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3268])).

tff(c_3518,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_3514,c_40])).

tff(c_3521,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_3518])).

tff(c_3522,plain,(
    ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3521])).

tff(c_3515,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3268])).

tff(c_467,plain,(
    ! [A_100] :
      ( v2_funct_2(A_100,k2_relat_1(A_100))
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(resolution,[status(thm)],[c_435,c_38])).

tff(c_3523,plain,(
    ! [B_302,A_303] :
      ( v2_funct_2(k7_relat_1(B_302,A_303),k9_relat_1(B_302,A_303))
      | ~ v1_funct_1(k7_relat_1(B_302,A_303))
      | ~ v1_relat_1(k7_relat_1(B_302,A_303))
      | ~ v1_relat_1(B_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_467])).

tff(c_3529,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_3523])).

tff(c_3552,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_3269,c_3515,c_3529])).

tff(c_3554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3522,c_3552])).

tff(c_3555,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3521])).

tff(c_6878,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_3555])).

tff(c_462,plain,(
    ! [A_99] :
      ( v4_relat_1(A_99,k1_relat_1(A_99))
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_372,c_24])).

tff(c_476,plain,(
    ! [A_101] :
      ( k7_relat_1(A_101,k1_relat_1(A_101)) = A_101
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(resolution,[status(thm)],[c_462,c_14])).

tff(c_485,plain,(
    ! [A_101] :
      ( k9_relat_1(A_101,k1_relat_1(A_101)) = k2_relat_1(A_101)
      | ~ v1_relat_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_12])).

tff(c_606,plain,(
    ! [A_101] :
      ( k9_relat_1(k2_funct_1(A_101),k2_relat_1(A_101)) = k1_relat_1(A_101)
      | ~ r1_tarski(k1_relat_1(A_101),k1_relat_1(A_101))
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101)
      | ~ v1_relat_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_591])).

tff(c_619,plain,(
    ! [A_101] :
      ( k9_relat_1(k2_funct_1(A_101),k2_relat_1(A_101)) = k1_relat_1(A_101)
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_606])).

tff(c_6909,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6878,c_619])).

tff(c_6934,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2994,c_6849,c_6909])).

tff(c_7115,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7017,c_24])).

tff(c_7154,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7115,c_14])).

tff(c_7157,plain,(
    k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7118,c_7154])).

tff(c_7189,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7157,c_12])).

tff(c_7197,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7118,c_6934,c_7189])).

tff(c_7114,plain,(
    v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7017,c_22])).

tff(c_7121,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_7114,c_40])).

tff(c_7124,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7118,c_7121])).

tff(c_7576,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7109,c_7197,c_7124])).

tff(c_2993,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2937])).

tff(c_2995,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2993])).

tff(c_7588,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7576,c_2995])).

tff(c_7600,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7588])).

tff(c_7601,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_2'))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2993])).

tff(c_7606,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7601])).

tff(c_7607,plain,(
    ! [A_449,B_450] :
      ( k2_funct_2(A_449,B_450) = k2_funct_1(B_450)
      | ~ m1_subset_1(B_450,k1_zfmisc_1(k2_zfmisc_1(A_449,A_449)))
      | ~ v3_funct_2(B_450,A_449,A_449)
      | ~ v1_funct_2(B_450,A_449,A_449)
      | ~ v1_funct_1(B_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_7613,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_7607])).

tff(c_7617,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_7613])).

tff(c_7705,plain,(
    ! [A_457,B_458] :
      ( v3_funct_2(k2_funct_2(A_457,B_458),A_457,A_457)
      | ~ m1_subset_1(B_458,k1_zfmisc_1(k2_zfmisc_1(A_457,A_457)))
      | ~ v3_funct_2(B_458,A_457,A_457)
      | ~ v1_funct_2(B_458,A_457,A_457)
      | ~ v1_funct_1(B_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7709,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_7705])).

tff(c_7713,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_7617,c_7709])).

tff(c_7717,plain,(
    ! [A_462,B_463] :
      ( m1_subset_1(k2_funct_2(A_462,B_463),k1_zfmisc_1(k2_zfmisc_1(A_462,A_462)))
      | ~ m1_subset_1(B_463,k1_zfmisc_1(k2_zfmisc_1(A_462,A_462)))
      | ~ v3_funct_2(B_463,A_462,A_462)
      | ~ v1_funct_2(B_463,A_462,A_462)
      | ~ v1_funct_1(B_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7747,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7617,c_7717])).

tff(c_7761,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_7747])).

tff(c_7777,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7761,c_34])).

tff(c_7806,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_7713,c_7777])).

tff(c_7808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7606,c_7806])).

tff(c_7810,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7601])).

tff(c_7809,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7601])).

tff(c_8335,plain,(
    ! [A_493,B_494] :
      ( k2_funct_2(A_493,B_494) = k2_funct_1(B_494)
      | ~ m1_subset_1(B_494,k1_zfmisc_1(k2_zfmisc_1(A_493,A_493)))
      | ~ v3_funct_2(B_494,A_493,A_493)
      | ~ v1_funct_2(B_494,A_493,A_493)
      | ~ v1_funct_1(B_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8341,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_8335])).

tff(c_8345,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_8341])).

tff(c_8930,plain,(
    ! [A_523,B_524] :
      ( m1_subset_1(k2_funct_2(A_523,B_524),k1_zfmisc_1(k2_zfmisc_1(A_523,A_523)))
      | ~ m1_subset_1(B_524,k1_zfmisc_1(k2_zfmisc_1(A_523,A_523)))
      | ~ v3_funct_2(B_524,A_523,A_523)
      | ~ v1_funct_2(B_524,A_523,A_523)
      | ~ v1_funct_1(B_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8960,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8345,c_8930])).

tff(c_8974,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_8960])).

tff(c_9022,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8974,c_24])).

tff(c_9034,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9022,c_14])).

tff(c_9037,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_9034])).

tff(c_7866,plain,(
    ! [A_466,B_467] :
      ( k2_funct_2(A_466,B_467) = k2_funct_1(B_467)
      | ~ m1_subset_1(B_467,k1_zfmisc_1(k2_zfmisc_1(A_466,A_466)))
      | ~ v3_funct_2(B_467,A_466,A_466)
      | ~ v1_funct_2(B_467,A_466,A_466)
      | ~ v1_funct_1(B_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_7872,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_7866])).

tff(c_7876,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_7872])).

tff(c_8214,plain,(
    ! [A_491,B_492] :
      ( m1_subset_1(k2_funct_2(A_491,B_492),k1_zfmisc_1(k2_zfmisc_1(A_491,A_491)))
      | ~ m1_subset_1(B_492,k1_zfmisc_1(k2_zfmisc_1(A_491,A_491)))
      | ~ v3_funct_2(B_492,A_491,A_491)
      | ~ v1_funct_2(B_492,A_491,A_491)
      | ~ v1_funct_1(B_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8244,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7876,c_8214])).

tff(c_8258,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_8244])).

tff(c_8306,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8258,c_24])).

tff(c_8318,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8306,c_14])).

tff(c_8321,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_8318])).

tff(c_7821,plain,(
    ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2901])).

tff(c_8328,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8321,c_7821])).

tff(c_8331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_8328])).

tff(c_8333,plain,(
    v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2901])).

tff(c_8597,plain,(
    ! [A_515,B_516] :
      ( m1_subset_1(k2_funct_2(A_515,B_516),k1_zfmisc_1(k2_zfmisc_1(A_515,A_515)))
      | ~ m1_subset_1(B_516,k1_zfmisc_1(k2_zfmisc_1(A_515,A_515)))
      | ~ v3_funct_2(B_516,A_515,A_515)
      | ~ v1_funct_2(B_516,A_515,A_515)
      | ~ v1_funct_1(B_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8627,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8345,c_8597])).

tff(c_8641,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_8627])).

tff(c_8689,plain,(
    v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8641,c_24])).

tff(c_8701,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8689,c_14])).

tff(c_8704,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_8701])).

tff(c_8332,plain,
    ( ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2901])).

tff(c_8353,plain,(
    ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8332])).

tff(c_8711,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8704,c_8353])).

tff(c_8715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2994,c_8711])).

tff(c_8716,plain,(
    v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_8332])).

tff(c_8720,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_8716,c_40])).

tff(c_8723,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8333,c_8720])).

tff(c_8733,plain,(
    ~ v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8723])).

tff(c_8717,plain,(
    v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8332])).

tff(c_8734,plain,(
    ! [B_519,A_520] :
      ( v2_funct_2(k7_relat_1(B_519,A_520),k9_relat_1(B_519,A_520))
      | ~ v1_funct_1(k7_relat_1(B_519,A_520))
      | ~ v1_relat_1(k7_relat_1(B_519,A_520))
      | ~ v1_relat_1(B_519) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_467])).

tff(c_8743,plain,
    ( v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_8734])).

tff(c_8766,plain,(
    v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_8333,c_8717,c_8743])).

tff(c_8768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8733,c_8766])).

tff(c_8769,plain,(
    k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'),'#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8723])).

tff(c_9051,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9037,c_8769])).

tff(c_9076,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9051,c_619])).

tff(c_9101,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2994,c_7810,c_7809,c_9076])).

tff(c_7602,plain,(
    r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2993])).

tff(c_7605,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_7602,c_2])).

tff(c_8334,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7605])).

tff(c_9138,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9101,c_8334])).

tff(c_9142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9138])).

tff(c_9143,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7605])).

tff(c_9150,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9143,c_485])).

tff(c_9172,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2994,c_2847,c_2442,c_9150])).

tff(c_56,plain,(
    ! [A_40] :
      ( m1_subset_1(A_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_10232,plain,(
    ! [C_569,D_564,F_568,B_565,E_566,A_567] :
      ( k1_partfun1(A_567,B_565,C_569,D_564,E_566,F_568) = k5_relat_1(E_566,F_568)
      | ~ m1_subset_1(F_568,k1_zfmisc_1(k2_zfmisc_1(C_569,D_564)))
      | ~ v1_funct_1(F_568)
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(A_567,B_565)))
      | ~ v1_funct_1(E_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_11877,plain,(
    ! [A_600,B_601,A_602,E_603] :
      ( k1_partfun1(A_600,B_601,k1_relat_1(A_602),k2_relat_1(A_602),E_603,A_602) = k5_relat_1(E_603,A_602)
      | ~ m1_subset_1(E_603,k1_zfmisc_1(k2_zfmisc_1(A_600,B_601)))
      | ~ v1_funct_1(E_603)
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(resolution,[status(thm)],[c_56,c_10232])).

tff(c_11897,plain,(
    ! [A_602] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_602),k2_relat_1(A_602),'#skF_2',A_602) = k5_relat_1('#skF_2',A_602)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_funct_1(A_602)
      | ~ v1_relat_1(A_602) ) ),
    inference(resolution,[status(thm)],[c_64,c_11877])).

tff(c_11921,plain,(
    ! [A_604] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_604),k2_relat_1(A_604),'#skF_2',A_604) = k5_relat_1('#skF_2',A_604)
      | ~ v1_funct_1(A_604)
      | ~ v1_relat_1(A_604) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11897])).

tff(c_11948,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1',k2_relat_1(k2_funct_1('#skF_2')),'#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9143,c_11921])).

tff(c_11973,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2994,c_9172,c_11948])).

tff(c_9245,plain,(
    ! [A_531,B_532] :
      ( k2_funct_2(A_531,B_532) = k2_funct_1(B_532)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(k2_zfmisc_1(A_531,A_531)))
      | ~ v3_funct_2(B_532,A_531,A_531)
      | ~ v1_funct_2(B_532,A_531,A_531)
      | ~ v1_funct_1(B_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_9251,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_9245])).

tff(c_9255,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_9251])).

tff(c_62,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_100,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_9257,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9255,c_100])).

tff(c_11978,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11973,c_9257])).

tff(c_11985,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_11978])).

tff(c_11988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_520,c_369,c_2417,c_11985])).

tff(c_11989,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_19166,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19162,c_11989])).

tff(c_20126,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20012,c_19166])).

tff(c_20139,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_20126])).

tff(c_20142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_70,c_12372,c_12253,c_12226,c_20139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.12/4.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.70/4.32  
% 10.70/4.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.70/4.33  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.70/4.33  
% 10.70/4.33  %Foreground sorts:
% 10.70/4.33  
% 10.70/4.33  
% 10.70/4.33  %Background operators:
% 10.70/4.33  
% 10.70/4.33  
% 10.70/4.33  %Foreground operators:
% 10.70/4.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.70/4.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.70/4.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.70/4.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.70/4.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.70/4.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.70/4.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.70/4.33  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 10.70/4.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.70/4.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.70/4.33  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.70/4.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.70/4.33  tff('#skF_2', type, '#skF_2': $i).
% 10.70/4.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.70/4.33  tff('#skF_1', type, '#skF_1': $i).
% 10.70/4.33  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.70/4.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.70/4.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.70/4.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.70/4.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.70/4.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.70/4.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.70/4.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.70/4.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.70/4.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.70/4.33  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 10.70/4.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.70/4.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.70/4.33  
% 10.93/4.38  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.93/4.38  tff(f_168, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 10.93/4.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.93/4.38  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.93/4.38  tff(f_145, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.93/4.38  tff(f_87, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 10.93/4.38  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.93/4.38  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.93/4.38  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.93/4.38  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 10.93/4.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.93/4.38  tff(f_155, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.93/4.38  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.93/4.38  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 10.93/4.38  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 10.93/4.38  tff(f_143, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.93/4.38  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 10.93/4.38  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.93/4.38  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.93/4.38  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.93/4.38  tff(c_87, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.93/4.38  tff(c_93, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_87])).
% 10.93/4.38  tff(c_99, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_93])).
% 10.93/4.38  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.93/4.38  tff(c_66, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.93/4.38  tff(c_12352, plain, (![C_655, A_656, B_657]: (v2_funct_1(C_655) | ~v3_funct_2(C_655, A_656, B_657) | ~v1_funct_1(C_655) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_656, B_657))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.38  tff(c_12364, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_12352])).
% 10.93/4.38  tff(c_12372, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_12364])).
% 10.93/4.38  tff(c_54, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.93/4.38  tff(c_30, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.93/4.38  tff(c_71, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_30])).
% 10.93/4.38  tff(c_12248, plain, (![A_646, B_647, D_648]: (r2_relset_1(A_646, B_647, D_648, D_648) | ~m1_subset_1(D_648, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.93/4.38  tff(c_12253, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_71, c_12248])).
% 10.93/4.38  tff(c_11999, plain, (![C_608, B_609, A_610]: (v5_relat_1(C_608, B_609) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_610, B_609))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.93/4.38  tff(c_12007, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_11999])).
% 10.93/4.38  tff(c_12085, plain, (![B_624, A_625]: (k2_relat_1(B_624)=A_625 | ~v2_funct_2(B_624, A_625) | ~v5_relat_1(B_624, A_625) | ~v1_relat_1(B_624))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.93/4.38  tff(c_12091, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12007, c_12085])).
% 10.93/4.38  tff(c_12097, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_12091])).
% 10.93/4.38  tff(c_12098, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_12097])).
% 10.93/4.38  tff(c_12209, plain, (![C_643, B_644, A_645]: (v2_funct_2(C_643, B_644) | ~v3_funct_2(C_643, A_645, B_644) | ~v1_funct_1(C_643) | ~m1_subset_1(C_643, k1_zfmisc_1(k2_zfmisc_1(A_645, B_644))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.38  tff(c_12218, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_12209])).
% 10.93/4.38  tff(c_12223, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_12218])).
% 10.93/4.38  tff(c_12225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12098, c_12223])).
% 10.93/4.38  tff(c_12226, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_12097])).
% 10.93/4.38  tff(c_18, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.93/4.38  tff(c_73, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_partfun1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_18])).
% 10.93/4.38  tff(c_68, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.93/4.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.93/4.38  tff(c_12257, plain, (![A_651]: (m1_subset_1(A_651, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_651), k2_relat_1(A_651)))) | ~v1_funct_1(A_651) | ~v1_relat_1(A_651))), inference(cnfTransformation, [status(thm)], [f_155])).
% 10.93/4.38  tff(c_12271, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12226, c_12257])).
% 10.93/4.38  tff(c_12282, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_12271])).
% 10.93/4.38  tff(c_24, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.93/4.38  tff(c_12295, plain, (v4_relat_1('#skF_2', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_12282, c_24])).
% 10.93/4.38  tff(c_14, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.93/4.38  tff(c_12303, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12295, c_14])).
% 10.93/4.38  tff(c_12306, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_12303])).
% 10.93/4.38  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.93/4.38  tff(c_12310, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12306, c_12])).
% 10.93/4.38  tff(c_12314, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_12226, c_12310])).
% 10.93/4.38  tff(c_12476, plain, (![A_669, B_670]: (k9_relat_1(k2_funct_1(A_669), k9_relat_1(A_669, B_670))=B_670 | ~r1_tarski(B_670, k1_relat_1(A_669)) | ~v2_funct_1(A_669) | ~v1_funct_1(A_669) | ~v1_relat_1(A_669))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.93/4.38  tff(c_12494, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12314, c_12476])).
% 10.93/4.38  tff(c_12506, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_12372, c_6, c_12494])).
% 10.93/4.38  tff(c_22, plain, (![C_18, B_17, A_16]: (v5_relat_1(C_18, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.93/4.38  tff(c_12329, plain, (![A_653]: (v5_relat_1(A_653, k2_relat_1(A_653)) | ~v1_funct_1(A_653) | ~v1_relat_1(A_653))), inference(resolution, [status(thm)], [c_12257, c_22])).
% 10.93/4.38  tff(c_12568, plain, (![B_676, A_677]: (v5_relat_1(k7_relat_1(B_676, A_677), k9_relat_1(B_676, A_677)) | ~v1_funct_1(k7_relat_1(B_676, A_677)) | ~v1_relat_1(k7_relat_1(B_676, A_677)) | ~v1_relat_1(B_676))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12329])).
% 10.93/4.38  tff(c_12577, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12506, c_12568])).
% 10.93/4.38  tff(c_12720, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_12577])).
% 10.93/4.38  tff(c_12722, plain, (![A_687, B_688]: (k2_funct_2(A_687, B_688)=k2_funct_1(B_688) | ~m1_subset_1(B_688, k1_zfmisc_1(k2_zfmisc_1(A_687, A_687))) | ~v3_funct_2(B_688, A_687, A_687) | ~v1_funct_2(B_688, A_687, A_687) | ~v1_funct_1(B_688))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.38  tff(c_12728, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_12722])).
% 10.93/4.38  tff(c_12732, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_12728])).
% 10.93/4.38  tff(c_12888, plain, (![A_702, B_703]: (m1_subset_1(k2_funct_2(A_702, B_703), k1_zfmisc_1(k2_zfmisc_1(A_702, A_702))) | ~m1_subset_1(B_703, k1_zfmisc_1(k2_zfmisc_1(A_702, A_702))) | ~v3_funct_2(B_703, A_702, A_702) | ~v1_funct_2(B_703, A_702, A_702) | ~v1_funct_1(B_703))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.38  tff(c_12918, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12732, c_12888])).
% 10.93/4.38  tff(c_12932, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_12918])).
% 10.93/4.38  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.93/4.38  tff(c_12959, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_12932, c_8])).
% 10.93/4.38  tff(c_12983, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12959])).
% 10.93/4.38  tff(c_12985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12720, c_12983])).
% 10.93/4.38  tff(c_12987, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_12577])).
% 10.93/4.38  tff(c_14969, plain, (![A_791, B_792]: (k2_funct_2(A_791, B_792)=k2_funct_1(B_792) | ~m1_subset_1(B_792, k1_zfmisc_1(k2_zfmisc_1(A_791, A_791))) | ~v3_funct_2(B_792, A_791, A_791) | ~v1_funct_2(B_792, A_791, A_791) | ~v1_funct_1(B_792))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.38  tff(c_14975, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_14969])).
% 10.93/4.38  tff(c_14979, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_14975])).
% 10.93/4.38  tff(c_12708, plain, (![A_683, B_684]: (v1_funct_1(k2_funct_2(A_683, B_684)) | ~m1_subset_1(B_684, k1_zfmisc_1(k2_zfmisc_1(A_683, A_683))) | ~v3_funct_2(B_684, A_683, A_683) | ~v1_funct_2(B_684, A_683, A_683) | ~v1_funct_1(B_684))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.38  tff(c_12714, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_12708])).
% 10.93/4.38  tff(c_12718, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_12714])).
% 10.93/4.38  tff(c_14980, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14979, c_12718])).
% 10.93/4.38  tff(c_15182, plain, (![A_800, B_801]: (v3_funct_2(k2_funct_2(A_800, B_801), A_800, A_800) | ~m1_subset_1(B_801, k1_zfmisc_1(k2_zfmisc_1(A_800, A_800))) | ~v3_funct_2(B_801, A_800, A_800) | ~v1_funct_2(B_801, A_800, A_800) | ~v1_funct_1(B_801))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_15186, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_15182])).
% 10.93/4.39  tff(c_15190, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_14979, c_15186])).
% 10.93/4.39  tff(c_15465, plain, (![A_808, B_809]: (m1_subset_1(k2_funct_2(A_808, B_809), k1_zfmisc_1(k2_zfmisc_1(A_808, A_808))) | ~m1_subset_1(B_809, k1_zfmisc_1(k2_zfmisc_1(A_808, A_808))) | ~v3_funct_2(B_809, A_808, A_808) | ~v1_funct_2(B_809, A_808, A_808) | ~v1_funct_1(B_809))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_15495, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14979, c_15465])).
% 10.93/4.39  tff(c_15509, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_15495])).
% 10.93/4.39  tff(c_32, plain, (![C_26, B_25, A_24]: (v2_funct_2(C_26, B_25) | ~v3_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.39  tff(c_15522, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_15509, c_32])).
% 10.93/4.39  tff(c_15551, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14980, c_15190, c_15522])).
% 10.93/4.39  tff(c_15557, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_15509, c_22])).
% 10.93/4.39  tff(c_40, plain, (![B_28, A_27]: (k2_relat_1(B_28)=A_27 | ~v2_funct_2(B_28, A_27) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.93/4.39  tff(c_15569, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_15557, c_40])).
% 10.93/4.39  tff(c_15572, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12987, c_15551, c_15569])).
% 10.93/4.39  tff(c_15556, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_15509, c_24])).
% 10.93/4.39  tff(c_15563, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_15556, c_14])).
% 10.93/4.39  tff(c_15566, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12987, c_15563])).
% 10.93/4.39  tff(c_14169, plain, (![A_758, B_759]: (k2_funct_2(A_758, B_759)=k2_funct_1(B_759) | ~m1_subset_1(B_759, k1_zfmisc_1(k2_zfmisc_1(A_758, A_758))) | ~v3_funct_2(B_759, A_758, A_758) | ~v1_funct_2(B_759, A_758, A_758) | ~v1_funct_1(B_759))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_14175, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_14169])).
% 10.93/4.39  tff(c_14179, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_14175])).
% 10.93/4.39  tff(c_14804, plain, (![A_789, B_790]: (m1_subset_1(k2_funct_2(A_789, B_790), k1_zfmisc_1(k2_zfmisc_1(A_789, A_789))) | ~m1_subset_1(B_790, k1_zfmisc_1(k2_zfmisc_1(A_789, A_789))) | ~v3_funct_2(B_790, A_789, A_789) | ~v1_funct_2(B_790, A_789, A_789) | ~v1_funct_1(B_790))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_14834, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14179, c_14804])).
% 10.93/4.39  tff(c_14848, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_14834])).
% 10.93/4.39  tff(c_14895, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_14848, c_24])).
% 10.93/4.39  tff(c_14902, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_14895, c_14])).
% 10.93/4.39  tff(c_14905, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12987, c_14902])).
% 10.93/4.39  tff(c_13587, plain, (![A_730, B_731]: (k2_funct_2(A_730, B_731)=k2_funct_1(B_731) | ~m1_subset_1(B_731, k1_zfmisc_1(k2_zfmisc_1(A_730, A_730))) | ~v3_funct_2(B_731, A_730, A_730) | ~v1_funct_2(B_731, A_730, A_730) | ~v1_funct_1(B_731))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_13593, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_13587])).
% 10.93/4.39  tff(c_13597, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_13593])).
% 10.93/4.39  tff(c_13598, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13597, c_12718])).
% 10.93/4.39  tff(c_14008, plain, (![A_756, B_757]: (m1_subset_1(k2_funct_2(A_756, B_757), k1_zfmisc_1(k2_zfmisc_1(A_756, A_756))) | ~m1_subset_1(B_757, k1_zfmisc_1(k2_zfmisc_1(A_756, A_756))) | ~v3_funct_2(B_757, A_756, A_756) | ~v1_funct_2(B_757, A_756, A_756) | ~v1_funct_1(B_757))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_14038, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13597, c_14008])).
% 10.93/4.39  tff(c_14052, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_14038])).
% 10.93/4.39  tff(c_14099, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_14052, c_24])).
% 10.93/4.39  tff(c_14106, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_14099, c_14])).
% 10.93/4.39  tff(c_14109, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12987, c_14106])).
% 10.93/4.39  tff(c_12986, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_12577])).
% 10.93/4.39  tff(c_12988, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_12986])).
% 10.93/4.39  tff(c_14161, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14109, c_12988])).
% 10.93/4.39  tff(c_14165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13598, c_14161])).
% 10.93/4.39  tff(c_14166, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_12986])).
% 10.93/4.39  tff(c_14168, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_14166])).
% 10.93/4.39  tff(c_14956, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14905, c_14168])).
% 10.93/4.39  tff(c_14960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12987, c_14956])).
% 10.93/4.39  tff(c_14962, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_14166])).
% 10.93/4.39  tff(c_14961, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_14166])).
% 10.93/4.39  tff(c_14965, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2') | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_14961, c_40])).
% 10.93/4.39  tff(c_14968, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2') | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14962, c_14965])).
% 10.93/4.39  tff(c_14993, plain, (~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_14968])).
% 10.93/4.39  tff(c_14167, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_12986])).
% 10.93/4.39  tff(c_38, plain, (![B_28]: (v2_funct_2(B_28, k2_relat_1(B_28)) | ~v5_relat_1(B_28, k2_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.93/4.39  tff(c_12374, plain, (![A_658]: (v2_funct_2(A_658, k2_relat_1(A_658)) | ~v1_funct_1(A_658) | ~v1_relat_1(A_658))), inference(resolution, [status(thm)], [c_12329, c_38])).
% 10.93/4.39  tff(c_12634, plain, (![B_680, A_681]: (v2_funct_2(k7_relat_1(B_680, A_681), k9_relat_1(B_680, A_681)) | ~v1_funct_1(k7_relat_1(B_680, A_681)) | ~v1_relat_1(k7_relat_1(B_680, A_681)) | ~v1_relat_1(B_680))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12374])).
% 10.93/4.39  tff(c_12640, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12506, c_12634])).
% 10.93/4.39  tff(c_15007, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12987, c_14962, c_14167, c_12640])).
% 10.93/4.39  tff(c_15008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14993, c_15007])).
% 10.93/4.39  tff(c_15009, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))=k1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_14968])).
% 10.93/4.39  tff(c_15626, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15566, c_15009])).
% 10.93/4.39  tff(c_15631, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15572, c_15626])).
% 10.93/4.39  tff(c_12009, plain, (![C_612, A_613, B_614]: (v4_relat_1(C_612, A_613) | ~m1_subset_1(C_612, k1_zfmisc_1(k2_zfmisc_1(A_613, B_614))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.93/4.39  tff(c_12017, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_12009])).
% 10.93/4.39  tff(c_12028, plain, (![B_618, A_619]: (k7_relat_1(B_618, A_619)=B_618 | ~v4_relat_1(B_618, A_619) | ~v1_relat_1(B_618))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.93/4.39  tff(c_12034, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12017, c_12028])).
% 10.93/4.39  tff(c_12040, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_12034])).
% 10.93/4.39  tff(c_12044, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12040, c_12])).
% 10.93/4.39  tff(c_12048, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_12044])).
% 10.93/4.39  tff(c_12228, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12226, c_12048])).
% 10.93/4.39  tff(c_12497, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12228, c_12476])).
% 10.93/4.39  tff(c_12508, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_12372, c_12497])).
% 10.93/4.39  tff(c_12518, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12506, c_12508])).
% 10.93/4.39  tff(c_12519, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_12518])).
% 10.93/4.39  tff(c_15653, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15631, c_12519])).
% 10.93/4.39  tff(c_15663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_15653])).
% 10.93/4.39  tff(c_15664, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_12518])).
% 10.93/4.39  tff(c_16, plain, (![A_12, B_14]: (k9_relat_1(k2_funct_1(A_12), k9_relat_1(A_12, B_14))=B_14 | ~r1_tarski(B_14, k1_relat_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.93/4.39  tff(c_12514, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12506, c_16])).
% 10.93/4.39  tff(c_15872, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_15664, c_12514])).
% 10.93/4.39  tff(c_15873, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_15872])).
% 10.93/4.39  tff(c_15903, plain, (![A_826, B_827]: (k2_funct_2(A_826, B_827)=k2_funct_1(B_827) | ~m1_subset_1(B_827, k1_zfmisc_1(k2_zfmisc_1(A_826, A_826))) | ~v3_funct_2(B_827, A_826, A_826) | ~v1_funct_2(B_827, A_826, A_826) | ~v1_funct_1(B_827))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_15909, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_15903])).
% 10.93/4.39  tff(c_15913, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_15909])).
% 10.93/4.39  tff(c_16088, plain, (![A_843, B_844]: (m1_subset_1(k2_funct_2(A_843, B_844), k1_zfmisc_1(k2_zfmisc_1(A_843, A_843))) | ~m1_subset_1(B_844, k1_zfmisc_1(k2_zfmisc_1(A_843, A_843))) | ~v3_funct_2(B_844, A_843, A_843) | ~v1_funct_2(B_844, A_843, A_843) | ~v1_funct_1(B_844))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_16118, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15913, c_16088])).
% 10.93/4.39  tff(c_16132, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_16118])).
% 10.93/4.39  tff(c_16159, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_16132, c_8])).
% 10.93/4.39  tff(c_16183, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16159])).
% 10.93/4.39  tff(c_16185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15873, c_16183])).
% 10.93/4.39  tff(c_16187, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_15872])).
% 10.93/4.39  tff(c_18572, plain, (![A_957, B_958]: (k2_funct_2(A_957, B_958)=k2_funct_1(B_958) | ~m1_subset_1(B_958, k1_zfmisc_1(k2_zfmisc_1(A_957, A_957))) | ~v3_funct_2(B_958, A_957, A_957) | ~v1_funct_2(B_958, A_957, A_957) | ~v1_funct_1(B_958))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_18578, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_18572])).
% 10.93/4.39  tff(c_18582, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_18578])).
% 10.93/4.39  tff(c_15824, plain, (![A_819, B_820]: (v1_funct_1(k2_funct_2(A_819, B_820)) | ~m1_subset_1(B_820, k1_zfmisc_1(k2_zfmisc_1(A_819, A_819))) | ~v3_funct_2(B_820, A_819, A_819) | ~v1_funct_2(B_820, A_819, A_819) | ~v1_funct_1(B_820))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_15830, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_15824])).
% 10.93/4.39  tff(c_15834, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_15830])).
% 10.93/4.39  tff(c_18583, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18582, c_15834])).
% 10.93/4.39  tff(c_16217, plain, (![A_846, B_847]: (k2_funct_2(A_846, B_847)=k2_funct_1(B_847) | ~m1_subset_1(B_847, k1_zfmisc_1(k2_zfmisc_1(A_846, A_846))) | ~v3_funct_2(B_847, A_846, A_846) | ~v1_funct_2(B_847, A_846, A_846) | ~v1_funct_1(B_847))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_16223, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_16217])).
% 10.93/4.39  tff(c_16227, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_16223])).
% 10.93/4.39  tff(c_16228, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16227, c_15834])).
% 10.93/4.39  tff(c_16769, plain, (![A_881, B_882]: (v1_funct_2(k2_funct_2(A_881, B_882), A_881, A_881) | ~m1_subset_1(B_882, k1_zfmisc_1(k2_zfmisc_1(A_881, A_881))) | ~v3_funct_2(B_882, A_881, A_881) | ~v1_funct_2(B_882, A_881, A_881) | ~v1_funct_1(B_882))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_16773, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_16769])).
% 10.93/4.39  tff(c_16777, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_16227, c_16773])).
% 10.93/4.39  tff(c_16909, plain, (![A_883, B_884]: (v3_funct_2(k2_funct_2(A_883, B_884), A_883, A_883) | ~m1_subset_1(B_884, k1_zfmisc_1(k2_zfmisc_1(A_883, A_883))) | ~v3_funct_2(B_884, A_883, A_883) | ~v1_funct_2(B_884, A_883, A_883) | ~v1_funct_1(B_884))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_16913, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_16909])).
% 10.93/4.39  tff(c_16917, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_16227, c_16913])).
% 10.93/4.39  tff(c_17419, plain, (![A_899, B_900]: (m1_subset_1(k2_funct_2(A_899, B_900), k1_zfmisc_1(k2_zfmisc_1(A_899, A_899))) | ~m1_subset_1(B_900, k1_zfmisc_1(k2_zfmisc_1(A_899, A_899))) | ~v3_funct_2(B_900, A_899, A_899) | ~v1_funct_2(B_900, A_899, A_899) | ~v1_funct_1(B_900))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_17449, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16227, c_17419])).
% 10.93/4.39  tff(c_17463, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_17449])).
% 10.93/4.39  tff(c_52, plain, (![A_37, B_38]: (k2_funct_2(A_37, B_38)=k2_funct_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))) | ~v3_funct_2(B_38, A_37, A_37) | ~v1_funct_2(B_38, A_37, A_37) | ~v1_funct_1(B_38))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_17470, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_17463, c_52])).
% 10.93/4.39  tff(c_17499, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16777, c_16917, c_17470])).
% 10.93/4.39  tff(c_42, plain, (![A_29, B_30]: (m1_subset_1(k2_funct_2(A_29, B_30), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_17670, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17499, c_42])).
% 10.93/4.39  tff(c_17674, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16777, c_16917, c_17463, c_17670])).
% 10.93/4.39  tff(c_17743, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_17674, c_8])).
% 10.93/4.39  tff(c_17773, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_17743])).
% 10.93/4.39  tff(c_48, plain, (![A_29, B_30]: (v1_funct_1(k2_funct_2(A_29, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_17473, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_17463, c_48])).
% 10.93/4.39  tff(c_17502, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16777, c_16917, c_17473])).
% 10.93/4.39  tff(c_17666, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17499, c_17502])).
% 10.93/4.39  tff(c_44, plain, (![A_29, B_30]: (v3_funct_2(k2_funct_2(A_29, B_30), A_29, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_17465, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_17463, c_44])).
% 10.93/4.39  tff(c_17493, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16777, c_16917, c_17465])).
% 10.93/4.39  tff(c_17665, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17499, c_17493])).
% 10.93/4.39  tff(c_17729, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_17674, c_32])).
% 10.93/4.39  tff(c_17764, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17666, c_17665, c_17729])).
% 10.93/4.39  tff(c_17770, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_17674, c_22])).
% 10.93/4.39  tff(c_17783, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_17770, c_40])).
% 10.93/4.39  tff(c_17786, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17773, c_17764, c_17783])).
% 10.93/4.39  tff(c_17769, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_17674, c_24])).
% 10.93/4.39  tff(c_17776, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_17769, c_14])).
% 10.93/4.39  tff(c_17779, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_17773, c_17776])).
% 10.93/4.39  tff(c_17841, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_17779, c_12])).
% 10.93/4.39  tff(c_17849, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17773, c_17786, c_17841])).
% 10.93/4.39  tff(c_34, plain, (![C_26, A_24, B_25]: (v2_funct_1(C_26) | ~v3_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.39  tff(c_17479, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_17463, c_34])).
% 10.93/4.39  tff(c_17508, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16917, c_17479])).
% 10.93/4.39  tff(c_17510, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_17463, c_24])).
% 10.93/4.39  tff(c_17517, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_17510, c_14])).
% 10.93/4.39  tff(c_17520, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_17517])).
% 10.93/4.39  tff(c_16365, plain, (![A_861, B_862]: (m1_subset_1(k2_funct_2(A_861, B_862), k1_zfmisc_1(k2_zfmisc_1(A_861, A_861))) | ~m1_subset_1(B_862, k1_zfmisc_1(k2_zfmisc_1(A_861, A_861))) | ~v3_funct_2(B_862, A_861, A_861) | ~v1_funct_2(B_862, A_861, A_861) | ~v1_funct_1(B_862))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_16395, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16227, c_16365])).
% 10.93/4.39  tff(c_16409, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_16395])).
% 10.93/4.39  tff(c_16456, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_16409, c_24])).
% 10.93/4.39  tff(c_16463, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_16456, c_14])).
% 10.93/4.39  tff(c_16466, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_16463])).
% 10.93/4.39  tff(c_15666, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15664, c_12506])).
% 10.93/4.39  tff(c_15835, plain, (![B_821, A_822]: (v2_funct_2(k7_relat_1(B_821, A_822), k9_relat_1(B_821, A_822)) | ~v1_funct_1(k7_relat_1(B_821, A_822)) | ~v1_relat_1(k7_relat_1(B_821, A_822)) | ~v1_relat_1(B_821))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12374])).
% 10.93/4.39  tff(c_15841, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15666, c_15835])).
% 10.93/4.39  tff(c_16243, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_15841])).
% 10.93/4.39  tff(c_16244, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_16243])).
% 10.93/4.39  tff(c_16537, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16466, c_16244])).
% 10.93/4.39  tff(c_16540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16187, c_16537])).
% 10.93/4.39  tff(c_16542, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_16243])).
% 10.93/4.39  tff(c_16610, plain, (![A_879, B_880]: (m1_subset_1(k2_funct_2(A_879, B_880), k1_zfmisc_1(k2_zfmisc_1(A_879, A_879))) | ~m1_subset_1(B_880, k1_zfmisc_1(k2_zfmisc_1(A_879, A_879))) | ~v3_funct_2(B_880, A_879, A_879) | ~v1_funct_2(B_880, A_879, A_879) | ~v1_funct_1(B_880))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_16640, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16227, c_16610])).
% 10.93/4.39  tff(c_16654, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_16640])).
% 10.93/4.39  tff(c_16701, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_16654, c_24])).
% 10.93/4.39  tff(c_16708, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_16701, c_14])).
% 10.93/4.39  tff(c_16711, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_16708])).
% 10.93/4.39  tff(c_16541, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_16243])).
% 10.93/4.39  tff(c_16543, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_16541])).
% 10.93/4.39  tff(c_16762, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16711, c_16543])).
% 10.93/4.39  tff(c_16766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16228, c_16762])).
% 10.93/4.39  tff(c_16767, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_16541])).
% 10.93/4.39  tff(c_16768, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_16541])).
% 10.93/4.39  tff(c_15769, plain, (![B_815, A_816]: (v5_relat_1(k7_relat_1(B_815, A_816), k9_relat_1(B_815, A_816)) | ~v1_funct_1(k7_relat_1(B_815, A_816)) | ~v1_relat_1(k7_relat_1(B_815, A_816)) | ~v1_relat_1(B_815))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12329])).
% 10.93/4.39  tff(c_15778, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15666, c_15769])).
% 10.93/4.39  tff(c_16779, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_16542, c_16768, c_15778])).
% 10.93/4.39  tff(c_16782, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_16779, c_40])).
% 10.93/4.39  tff(c_16785, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16542, c_16767, c_16782])).
% 10.93/4.39  tff(c_17534, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17520, c_16785])).
% 10.93/4.39  tff(c_12347, plain, (![A_654]: (v4_relat_1(A_654, k1_relat_1(A_654)) | ~v1_funct_1(A_654) | ~v1_relat_1(A_654))), inference(resolution, [status(thm)], [c_12257, c_24])).
% 10.93/4.39  tff(c_12383, plain, (![A_659]: (k7_relat_1(A_659, k1_relat_1(A_659))=A_659 | ~v1_funct_1(A_659) | ~v1_relat_1(A_659))), inference(resolution, [status(thm)], [c_12347, c_14])).
% 10.93/4.39  tff(c_12392, plain, (![A_659]: (k9_relat_1(A_659, k1_relat_1(A_659))=k2_relat_1(A_659) | ~v1_relat_1(A_659) | ~v1_funct_1(A_659) | ~v1_relat_1(A_659))), inference(superposition, [status(thm), theory('equality')], [c_12383, c_12])).
% 10.93/4.39  tff(c_12491, plain, (![A_659]: (k9_relat_1(k2_funct_1(A_659), k2_relat_1(A_659))=k1_relat_1(A_659) | ~r1_tarski(k1_relat_1(A_659), k1_relat_1(A_659)) | ~v2_funct_1(A_659) | ~v1_funct_1(A_659) | ~v1_relat_1(A_659) | ~v1_relat_1(A_659) | ~v1_funct_1(A_659) | ~v1_relat_1(A_659))), inference(superposition, [status(thm), theory('equality')], [c_12392, c_12476])).
% 10.93/4.39  tff(c_12504, plain, (![A_659]: (k9_relat_1(k2_funct_1(A_659), k2_relat_1(A_659))=k1_relat_1(A_659) | ~v2_funct_1(A_659) | ~v1_funct_1(A_659) | ~v1_relat_1(A_659))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12491])).
% 10.93/4.39  tff(c_17566, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17534, c_12504])).
% 10.93/4.39  tff(c_17591, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_16228, c_17508, c_17566])).
% 10.93/4.39  tff(c_17899, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17849, c_17591])).
% 10.93/4.39  tff(c_16186, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_15872])).
% 10.93/4.39  tff(c_16188, plain, (~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_16186])).
% 10.93/4.39  tff(c_17903, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17899, c_16188])).
% 10.93/4.39  tff(c_17909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_17903])).
% 10.93/4.39  tff(c_17910, plain, (~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_16186])).
% 10.93/4.39  tff(c_18593, plain, (~v2_funct_1(k2_funct_1('#skF_2')) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18583, c_17910])).
% 10.93/4.39  tff(c_18594, plain, (~v2_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_18593])).
% 10.93/4.39  tff(c_18642, plain, (![A_965, B_966]: (v3_funct_2(k2_funct_2(A_965, B_966), A_965, A_965) | ~m1_subset_1(B_966, k1_zfmisc_1(k2_zfmisc_1(A_965, A_965))) | ~v3_funct_2(B_966, A_965, A_965) | ~v1_funct_2(B_966, A_965, A_965) | ~v1_funct_1(B_966))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_18646, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_18642])).
% 10.93/4.39  tff(c_18650, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_18582, c_18646])).
% 10.93/4.39  tff(c_18654, plain, (![A_968, B_969]: (m1_subset_1(k2_funct_2(A_968, B_969), k1_zfmisc_1(k2_zfmisc_1(A_968, A_968))) | ~m1_subset_1(B_969, k1_zfmisc_1(k2_zfmisc_1(A_968, A_968))) | ~v3_funct_2(B_969, A_968, A_968) | ~v1_funct_2(B_969, A_968, A_968) | ~v1_funct_1(B_969))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_18684, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18582, c_18654])).
% 10.93/4.39  tff(c_18698, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_18684])).
% 10.93/4.39  tff(c_18714, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_18698, c_34])).
% 10.93/4.39  tff(c_18743, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18583, c_18650, c_18714])).
% 10.93/4.39  tff(c_18745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18594, c_18743])).
% 10.93/4.39  tff(c_18747, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_18593])).
% 10.93/4.39  tff(c_18746, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_18593])).
% 10.93/4.39  tff(c_18810, plain, (![A_976, B_977]: (v3_funct_2(k2_funct_2(A_976, B_977), A_976, A_976) | ~m1_subset_1(B_977, k1_zfmisc_1(k2_zfmisc_1(A_976, A_976))) | ~v3_funct_2(B_977, A_976, A_976) | ~v1_funct_2(B_977, A_976, A_976) | ~v1_funct_1(B_977))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_18814, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_18810])).
% 10.93/4.39  tff(c_18818, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_18582, c_18814])).
% 10.93/4.39  tff(c_18909, plain, (![A_984, B_985]: (m1_subset_1(k2_funct_2(A_984, B_985), k1_zfmisc_1(k2_zfmisc_1(A_984, A_984))) | ~m1_subset_1(B_985, k1_zfmisc_1(k2_zfmisc_1(A_984, A_984))) | ~v3_funct_2(B_985, A_984, A_984) | ~v1_funct_2(B_985, A_984, A_984) | ~v1_funct_1(B_985))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_18939, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18582, c_18909])).
% 10.93/4.39  tff(c_18953, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_18939])).
% 10.93/4.39  tff(c_18966, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_18953, c_32])).
% 10.93/4.39  tff(c_18995, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18583, c_18818, c_18966])).
% 10.93/4.39  tff(c_19001, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_18953, c_22])).
% 10.93/4.39  tff(c_19013, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_19001, c_40])).
% 10.93/4.39  tff(c_19016, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_18995, c_19013])).
% 10.93/4.39  tff(c_19020, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_19016, c_12504])).
% 10.93/4.39  tff(c_19045, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_18583, c_18747, c_18746, c_19020])).
% 10.93/4.39  tff(c_17911, plain, (r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_16186])).
% 10.93/4.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.93/4.39  tff(c_17914, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_17911, c_2])).
% 10.93/4.39  tff(c_18571, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_17914])).
% 10.93/4.39  tff(c_19061, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19045, c_18571])).
% 10.93/4.39  tff(c_19065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_19061])).
% 10.93/4.39  tff(c_19066, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_17914])).
% 10.93/4.39  tff(c_12276, plain, (![A_651]: (v4_relat_1(A_651, k1_relat_1(A_651)) | ~v1_funct_1(A_651) | ~v1_relat_1(A_651))), inference(resolution, [status(thm)], [c_12257, c_24])).
% 10.93/4.39  tff(c_19085, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_19066, c_12276])).
% 10.93/4.39  tff(c_19103, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16187, c_19085])).
% 10.93/4.39  tff(c_19110, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_19103])).
% 10.93/4.39  tff(c_19111, plain, (![A_986, B_987]: (k2_funct_2(A_986, B_987)=k2_funct_1(B_987) | ~m1_subset_1(B_987, k1_zfmisc_1(k2_zfmisc_1(A_986, A_986))) | ~v3_funct_2(B_987, A_986, A_986) | ~v1_funct_2(B_987, A_986, A_986) | ~v1_funct_1(B_987))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_19117, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_19111])).
% 10.93/4.39  tff(c_19121, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_19117])).
% 10.93/4.39  tff(c_19122, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19121, c_15834])).
% 10.93/4.39  tff(c_19127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19110, c_19122])).
% 10.93/4.39  tff(c_19129, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_19103])).
% 10.93/4.39  tff(c_19152, plain, (![A_988, B_989]: (k2_funct_2(A_988, B_989)=k2_funct_1(B_989) | ~m1_subset_1(B_989, k1_zfmisc_1(k2_zfmisc_1(A_988, A_988))) | ~v3_funct_2(B_989, A_988, A_988) | ~v1_funct_2(B_989, A_988, A_988) | ~v1_funct_1(B_989))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_19158, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_19152])).
% 10.93/4.39  tff(c_19162, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_19158])).
% 10.93/4.39  tff(c_19509, plain, (![F_1002, D_998, E_1000, B_999, A_1001, C_1003]: (k1_partfun1(A_1001, B_999, C_1003, D_998, E_1000, F_1002)=k5_relat_1(E_1000, F_1002) | ~m1_subset_1(F_1002, k1_zfmisc_1(k2_zfmisc_1(C_1003, D_998))) | ~v1_funct_1(F_1002) | ~m1_subset_1(E_1000, k1_zfmisc_1(k2_zfmisc_1(A_1001, B_999))) | ~v1_funct_1(E_1000))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.93/4.39  tff(c_19521, plain, (![A_1001, B_999, E_1000]: (k1_partfun1(A_1001, B_999, '#skF_1', '#skF_1', E_1000, '#skF_2')=k5_relat_1(E_1000, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1000, k1_zfmisc_1(k2_zfmisc_1(A_1001, B_999))) | ~v1_funct_1(E_1000))), inference(resolution, [status(thm)], [c_64, c_19509])).
% 10.93/4.39  tff(c_19553, plain, (![A_1004, B_1005, E_1006]: (k1_partfun1(A_1004, B_1005, '#skF_1', '#skF_1', E_1006, '#skF_2')=k5_relat_1(E_1006, '#skF_2') | ~m1_subset_1(E_1006, k1_zfmisc_1(k2_zfmisc_1(A_1004, B_1005))) | ~v1_funct_1(E_1006))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_19521])).
% 10.93/4.39  tff(c_19981, plain, (![A_1014, B_1015]: (k1_partfun1(A_1014, A_1014, '#skF_1', '#skF_1', k2_funct_2(A_1014, B_1015), '#skF_2')=k5_relat_1(k2_funct_2(A_1014, B_1015), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1014, B_1015)) | ~m1_subset_1(B_1015, k1_zfmisc_1(k2_zfmisc_1(A_1014, A_1014))) | ~v3_funct_2(B_1015, A_1014, A_1014) | ~v1_funct_2(B_1015, A_1014, A_1014) | ~v1_funct_1(B_1015))), inference(resolution, [status(thm)], [c_42, c_19553])).
% 10.93/4.39  tff(c_19995, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_19981])).
% 10.93/4.39  tff(c_20012, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_19129, c_19162, c_19162, c_19162, c_19995])).
% 10.93/4.39  tff(c_500, plain, (![C_102, A_103, B_104]: (v2_funct_1(C_102) | ~v3_funct_2(C_102, A_103, B_104) | ~v1_funct_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.39  tff(c_512, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_500])).
% 10.93/4.39  tff(c_520, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_512])).
% 10.93/4.39  tff(c_364, plain, (![A_92, B_93, D_94]: (r2_relset_1(A_92, B_93, D_94, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.93/4.39  tff(c_369, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_71, c_364])).
% 10.93/4.39  tff(c_177, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.93/4.39  tff(c_185, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_177])).
% 10.93/4.39  tff(c_195, plain, (![B_67, A_68]: (k2_relat_1(B_67)=A_68 | ~v2_funct_2(B_67, A_68) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.93/4.39  tff(c_201, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_185, c_195])).
% 10.93/4.39  tff(c_207, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_201])).
% 10.93/4.39  tff(c_208, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_207])).
% 10.93/4.39  tff(c_324, plain, (![C_88, B_89, A_90]: (v2_funct_2(C_88, B_89) | ~v3_funct_2(C_88, A_90, B_89) | ~v1_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.93/4.39  tff(c_333, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_324])).
% 10.93/4.39  tff(c_338, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_333])).
% 10.93/4.39  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_338])).
% 10.93/4.39  tff(c_341, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_207])).
% 10.93/4.39  tff(c_372, plain, (![A_96]: (m1_subset_1(A_96, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_96), k2_relat_1(A_96)))) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_155])).
% 10.93/4.39  tff(c_386, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_341, c_372])).
% 10.93/4.39  tff(c_397, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_386])).
% 10.93/4.39  tff(c_412, plain, (v4_relat_1('#skF_2', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_397, c_24])).
% 10.93/4.39  tff(c_418, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_412, c_14])).
% 10.93/4.39  tff(c_421, plain, (k7_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_418])).
% 10.93/4.39  tff(c_425, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_421, c_12])).
% 10.93/4.39  tff(c_429, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_341, c_425])).
% 10.93/4.39  tff(c_591, plain, (![A_114, B_115]: (k9_relat_1(k2_funct_1(A_114), k9_relat_1(A_114, B_115))=B_115 | ~r1_tarski(B_115, k1_relat_1(A_114)) | ~v2_funct_1(A_114) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.93/4.39  tff(c_609, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_429, c_591])).
% 10.93/4.39  tff(c_621, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_520, c_6, c_609])).
% 10.93/4.39  tff(c_435, plain, (![A_97]: (v5_relat_1(A_97, k2_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_372, c_22])).
% 10.93/4.39  tff(c_655, plain, (![B_117, A_118]: (v5_relat_1(k7_relat_1(B_117, A_118), k9_relat_1(B_117, A_118)) | ~v1_funct_1(k7_relat_1(B_117, A_118)) | ~v1_relat_1(k7_relat_1(B_117, A_118)) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_12, c_435])).
% 10.93/4.39  tff(c_664, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_621, c_655])).
% 10.93/4.39  tff(c_743, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_664])).
% 10.93/4.39  tff(c_831, plain, (![A_132, B_133]: (k2_funct_2(A_132, B_133)=k2_funct_1(B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_132, A_132))) | ~v3_funct_2(B_133, A_132, A_132) | ~v1_funct_2(B_133, A_132, A_132) | ~v1_funct_1(B_133))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_837, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_831])).
% 10.93/4.39  tff(c_841, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_837])).
% 10.93/4.39  tff(c_989, plain, (![A_146, B_147]: (m1_subset_1(k2_funct_2(A_146, B_147), k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~m1_subset_1(B_147, k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~v3_funct_2(B_147, A_146, A_146) | ~v1_funct_2(B_147, A_146, A_146) | ~v1_funct_1(B_147))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_1019, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_841, c_989])).
% 10.93/4.39  tff(c_1033, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_1019])).
% 10.93/4.39  tff(c_1060, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1033, c_8])).
% 10.93/4.39  tff(c_1084, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1060])).
% 10.93/4.39  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_743, c_1084])).
% 10.93/4.39  tff(c_1088, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_664])).
% 10.93/4.39  tff(c_629, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_621, c_16])).
% 10.93/4.39  tff(c_1090, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_629])).
% 10.93/4.39  tff(c_1091, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1090])).
% 10.93/4.39  tff(c_1181, plain, (![A_154, B_155]: (k2_funct_2(A_154, B_155)=k2_funct_1(B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(k2_zfmisc_1(A_154, A_154))) | ~v3_funct_2(B_155, A_154, A_154) | ~v1_funct_2(B_155, A_154, A_154) | ~v1_funct_1(B_155))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_1187, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1181])).
% 10.93/4.39  tff(c_1191, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1187])).
% 10.93/4.39  tff(c_1141, plain, (![A_150, B_151]: (v1_funct_1(k2_funct_2(A_150, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(k2_zfmisc_1(A_150, A_150))) | ~v3_funct_2(B_151, A_150, A_150) | ~v1_funct_2(B_151, A_150, A_150) | ~v1_funct_1(B_151))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_1147, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1141])).
% 10.93/4.39  tff(c_1151, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1147])).
% 10.93/4.39  tff(c_1192, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_1151])).
% 10.93/4.39  tff(c_1195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1091, c_1192])).
% 10.93/4.39  tff(c_1197, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1090])).
% 10.93/4.39  tff(c_1746, plain, (![A_193, B_194]: (k2_funct_2(A_193, B_194)=k2_funct_1(B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_1752, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1746])).
% 10.93/4.39  tff(c_1756, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1752])).
% 10.93/4.39  tff(c_1936, plain, (![A_197, B_198]: (v3_funct_2(k2_funct_2(A_197, B_198), A_197, A_197) | ~m1_subset_1(B_198, k1_zfmisc_1(k2_zfmisc_1(A_197, A_197))) | ~v3_funct_2(B_198, A_197, A_197) | ~v1_funct_2(B_198, A_197, A_197) | ~v1_funct_1(B_198))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_1940, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1936])).
% 10.93/4.39  tff(c_1944, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1756, c_1940])).
% 10.93/4.39  tff(c_2094, plain, (![A_202, B_203]: (m1_subset_1(k2_funct_2(A_202, B_203), k1_zfmisc_1(k2_zfmisc_1(A_202, A_202))) | ~m1_subset_1(B_203, k1_zfmisc_1(k2_zfmisc_1(A_202, A_202))) | ~v3_funct_2(B_203, A_202, A_202) | ~v1_funct_2(B_203, A_202, A_202) | ~v1_funct_1(B_203))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_2124, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_2094])).
% 10.93/4.39  tff(c_2138, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_2124])).
% 10.93/4.39  tff(c_2151, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2138, c_32])).
% 10.93/4.39  tff(c_2180, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1944, c_2151])).
% 10.93/4.39  tff(c_2186, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2138, c_24])).
% 10.93/4.39  tff(c_2198, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2186, c_14])).
% 10.93/4.39  tff(c_2201, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_2198])).
% 10.93/4.39  tff(c_2228, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2201, c_12])).
% 10.93/4.39  tff(c_2236, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_621, c_2228])).
% 10.93/4.39  tff(c_2185, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2138, c_22])).
% 10.93/4.39  tff(c_2192, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2185, c_40])).
% 10.93/4.39  tff(c_2195, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_2192])).
% 10.93/4.39  tff(c_2400, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_2236, c_2195])).
% 10.93/4.39  tff(c_109, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.93/4.39  tff(c_117, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_109])).
% 10.93/4.39  tff(c_118, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.93/4.39  tff(c_121, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_117, c_118])).
% 10.93/4.39  tff(c_124, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_121])).
% 10.93/4.39  tff(c_145, plain, (![B_58, A_59]: (k2_relat_1(k7_relat_1(B_58, A_59))=k9_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.93/4.39  tff(c_157, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_145])).
% 10.93/4.39  tff(c_163, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_157])).
% 10.93/4.39  tff(c_343, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_341, c_163])).
% 10.93/4.39  tff(c_612, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_343, c_591])).
% 10.93/4.39  tff(c_623, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_520, c_612])).
% 10.93/4.39  tff(c_633, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_623])).
% 10.93/4.39  tff(c_634, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_633])).
% 10.93/4.39  tff(c_2404, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_634])).
% 10.93/4.39  tff(c_2416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2404])).
% 10.93/4.39  tff(c_2417, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_633])).
% 10.93/4.39  tff(c_20, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.93/4.39  tff(c_72, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_partfun1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20])).
% 10.93/4.39  tff(c_2502, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_629])).
% 10.93/4.39  tff(c_2503, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2502])).
% 10.93/4.39  tff(c_2656, plain, (![A_231, B_232]: (k2_funct_2(A_231, B_232)=k2_funct_1(B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(k2_zfmisc_1(A_231, A_231))) | ~v3_funct_2(B_232, A_231, A_231) | ~v1_funct_2(B_232, A_231, A_231) | ~v1_funct_1(B_232))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_2662, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2656])).
% 10.93/4.39  tff(c_2666, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2662])).
% 10.93/4.39  tff(c_2748, plain, (![A_243, B_244]: (m1_subset_1(k2_funct_2(A_243, B_244), k1_zfmisc_1(k2_zfmisc_1(A_243, A_243))) | ~m1_subset_1(B_244, k1_zfmisc_1(k2_zfmisc_1(A_243, A_243))) | ~v3_funct_2(B_244, A_243, A_243) | ~v1_funct_2(B_244, A_243, A_243) | ~v1_funct_1(B_244))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_2778, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2666, c_2748])).
% 10.93/4.39  tff(c_2792, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_2778])).
% 10.93/4.39  tff(c_2819, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_2792, c_8])).
% 10.93/4.39  tff(c_2843, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2819])).
% 10.93/4.39  tff(c_2845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2503, c_2843])).
% 10.93/4.39  tff(c_2847, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2502])).
% 10.93/4.39  tff(c_2442, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_621])).
% 10.93/4.39  tff(c_2498, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_16])).
% 10.93/4.39  tff(c_2937, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2498])).
% 10.93/4.39  tff(c_2938, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2937])).
% 10.93/4.39  tff(c_2978, plain, (![A_254, B_255]: (k2_funct_2(A_254, B_255)=k2_funct_1(B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_zfmisc_1(A_254, A_254))) | ~v3_funct_2(B_255, A_254, A_254) | ~v1_funct_2(B_255, A_254, A_254) | ~v1_funct_1(B_255))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_2984, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2978])).
% 10.93/4.39  tff(c_2988, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2984])).
% 10.93/4.39  tff(c_2924, plain, (![A_249, B_250]: (v1_funct_1(k2_funct_2(A_249, B_250)) | ~m1_subset_1(B_250, k1_zfmisc_1(k2_zfmisc_1(A_249, A_249))) | ~v3_funct_2(B_250, A_249, A_249) | ~v1_funct_2(B_250, A_249, A_249) | ~v1_funct_1(B_250))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_2930, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2924])).
% 10.93/4.39  tff(c_2934, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_2930])).
% 10.93/4.39  tff(c_2989, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2988, c_2934])).
% 10.93/4.39  tff(c_2992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2938, c_2989])).
% 10.93/4.39  tff(c_2994, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2937])).
% 10.93/4.39  tff(c_3611, plain, (![A_304, B_305]: (k2_funct_2(A_304, B_305)=k2_funct_1(B_305) | ~m1_subset_1(B_305, k1_zfmisc_1(k2_zfmisc_1(A_304, A_304))) | ~v3_funct_2(B_305, A_304, A_304) | ~v1_funct_2(B_305, A_304, A_304) | ~v1_funct_1(B_305))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_3617, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3611])).
% 10.93/4.39  tff(c_3621, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3617])).
% 10.93/4.39  tff(c_6655, plain, (![A_418, B_419]: (v1_funct_2(k2_funct_2(A_418, B_419), A_418, A_418) | ~m1_subset_1(B_419, k1_zfmisc_1(k2_zfmisc_1(A_418, A_418))) | ~v3_funct_2(B_419, A_418, A_418) | ~v1_funct_2(B_419, A_418, A_418) | ~v1_funct_1(B_419))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_6659, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_6655])).
% 10.93/4.39  tff(c_6663, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3621, c_6659])).
% 10.93/4.39  tff(c_3717, plain, (![A_306, B_307]: (v3_funct_2(k2_funct_2(A_306, B_307), A_306, A_306) | ~m1_subset_1(B_307, k1_zfmisc_1(k2_zfmisc_1(A_306, A_306))) | ~v3_funct_2(B_307, A_306, A_306) | ~v1_funct_2(B_307, A_306, A_306) | ~v1_funct_1(B_307))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_3721, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3717])).
% 10.93/4.39  tff(c_3725, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3621, c_3721])).
% 10.93/4.39  tff(c_6760, plain, (![A_425, B_426]: (m1_subset_1(k2_funct_2(A_425, B_426), k1_zfmisc_1(k2_zfmisc_1(A_425, A_425))) | ~m1_subset_1(B_426, k1_zfmisc_1(k2_zfmisc_1(A_425, A_425))) | ~v3_funct_2(B_426, A_425, A_425) | ~v1_funct_2(B_426, A_425, A_425) | ~v1_funct_1(B_426))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_6790, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3621, c_6760])).
% 10.93/4.39  tff(c_6804, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_6790])).
% 10.93/4.39  tff(c_6811, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6804, c_52])).
% 10.93/4.39  tff(c_6840, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_6663, c_3725, c_6811])).
% 10.93/4.39  tff(c_6814, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6804, c_48])).
% 10.93/4.39  tff(c_6843, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_6663, c_3725, c_6814])).
% 10.93/4.39  tff(c_7009, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6840, c_6843])).
% 10.93/4.39  tff(c_6808, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6804, c_44])).
% 10.93/4.39  tff(c_6837, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_6663, c_3725, c_6808])).
% 10.93/4.39  tff(c_7019, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6840, c_6837])).
% 10.93/4.39  tff(c_7013, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6840, c_42])).
% 10.93/4.39  tff(c_7017, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_6663, c_3725, c_6804, c_7013])).
% 10.93/4.39  tff(c_7074, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_7017, c_32])).
% 10.93/4.39  tff(c_7109, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7009, c_7019, c_7074])).
% 10.93/4.39  tff(c_7088, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_7017, c_8])).
% 10.93/4.39  tff(c_7118, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7088])).
% 10.93/4.39  tff(c_6820, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6804, c_34])).
% 10.93/4.39  tff(c_6849, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_3725, c_6820])).
% 10.93/4.39  tff(c_6852, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_6804, c_24])).
% 10.93/4.39  tff(c_6864, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_6852, c_14])).
% 10.93/4.39  tff(c_6867, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_6864])).
% 10.93/4.39  tff(c_3038, plain, (![A_259, B_260]: (k2_funct_2(A_259, B_260)=k2_funct_1(B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_3044, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3038])).
% 10.93/4.39  tff(c_3048, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3044])).
% 10.93/4.39  tff(c_3136, plain, (![A_272, B_273]: (m1_subset_1(k2_funct_2(A_272, B_273), k1_zfmisc_1(k2_zfmisc_1(A_272, A_272))) | ~m1_subset_1(B_273, k1_zfmisc_1(k2_zfmisc_1(A_272, A_272))) | ~v3_funct_2(B_273, A_272, A_272) | ~v1_funct_2(B_273, A_272, A_272) | ~v1_funct_1(B_273))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_3166, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3048, c_3136])).
% 10.93/4.39  tff(c_3180, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_3166])).
% 10.93/4.39  tff(c_3228, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3180, c_24])).
% 10.93/4.39  tff(c_3240, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3228, c_14])).
% 10.93/4.39  tff(c_3243, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_3240])).
% 10.93/4.39  tff(c_2868, plain, (![B_246, A_247]: (v5_relat_1(k7_relat_1(B_246, A_247), k9_relat_1(B_246, A_247)) | ~v1_funct_1(k7_relat_1(B_246, A_247)) | ~v1_relat_1(k7_relat_1(B_246, A_247)) | ~v1_relat_1(B_246))), inference(superposition, [status(thm), theory('equality')], [c_12, c_435])).
% 10.93/4.39  tff(c_2877, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_2868])).
% 10.93/4.39  tff(c_2901, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2877])).
% 10.93/4.39  tff(c_2996, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_2901])).
% 10.93/4.39  tff(c_3264, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3243, c_2996])).
% 10.93/4.39  tff(c_3267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2847, c_3264])).
% 10.93/4.39  tff(c_3269, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_2901])).
% 10.93/4.39  tff(c_3312, plain, (![A_282, B_283]: (k2_funct_2(A_282, B_283)=k2_funct_1(B_283) | ~m1_subset_1(B_283, k1_zfmisc_1(k2_zfmisc_1(A_282, A_282))) | ~v3_funct_2(B_283, A_282, A_282) | ~v1_funct_2(B_283, A_282, A_282) | ~v1_funct_1(B_283))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_3318, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_3312])).
% 10.93/4.39  tff(c_3322, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_3318])).
% 10.93/4.39  tff(c_3381, plain, (![A_294, B_295]: (m1_subset_1(k2_funct_2(A_294, B_295), k1_zfmisc_1(k2_zfmisc_1(A_294, A_294))) | ~m1_subset_1(B_295, k1_zfmisc_1(k2_zfmisc_1(A_294, A_294))) | ~v3_funct_2(B_295, A_294, A_294) | ~v1_funct_2(B_295, A_294, A_294) | ~v1_funct_1(B_295))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_3411, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3322, c_3381])).
% 10.93/4.39  tff(c_3425, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_3411])).
% 10.93/4.39  tff(c_3473, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_3425, c_24])).
% 10.93/4.39  tff(c_3485, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3473, c_14])).
% 10.93/4.39  tff(c_3488, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_3485])).
% 10.93/4.39  tff(c_3268, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_2901])).
% 10.93/4.39  tff(c_3273, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_3268])).
% 10.93/4.39  tff(c_3509, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3488, c_3273])).
% 10.93/4.39  tff(c_3513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2994, c_3509])).
% 10.93/4.39  tff(c_3514, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_3268])).
% 10.93/4.39  tff(c_3518, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_3514, c_40])).
% 10.93/4.39  tff(c_3521, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_3518])).
% 10.93/4.39  tff(c_3522, plain, (~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3521])).
% 10.93/4.39  tff(c_3515, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_3268])).
% 10.93/4.39  tff(c_467, plain, (![A_100]: (v2_funct_2(A_100, k2_relat_1(A_100)) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(resolution, [status(thm)], [c_435, c_38])).
% 10.93/4.39  tff(c_3523, plain, (![B_302, A_303]: (v2_funct_2(k7_relat_1(B_302, A_303), k9_relat_1(B_302, A_303)) | ~v1_funct_1(k7_relat_1(B_302, A_303)) | ~v1_relat_1(k7_relat_1(B_302, A_303)) | ~v1_relat_1(B_302))), inference(superposition, [status(thm), theory('equality')], [c_12, c_467])).
% 10.93/4.39  tff(c_3529, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_3523])).
% 10.93/4.39  tff(c_3552, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_3269, c_3515, c_3529])).
% 10.93/4.39  tff(c_3554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3522, c_3552])).
% 10.93/4.39  tff(c_3555, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_3521])).
% 10.93/4.39  tff(c_6878, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_3555])).
% 10.93/4.39  tff(c_462, plain, (![A_99]: (v4_relat_1(A_99, k1_relat_1(A_99)) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(resolution, [status(thm)], [c_372, c_24])).
% 10.93/4.39  tff(c_476, plain, (![A_101]: (k7_relat_1(A_101, k1_relat_1(A_101))=A_101 | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(resolution, [status(thm)], [c_462, c_14])).
% 10.93/4.39  tff(c_485, plain, (![A_101]: (k9_relat_1(A_101, k1_relat_1(A_101))=k2_relat_1(A_101) | ~v1_relat_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_476, c_12])).
% 10.93/4.39  tff(c_606, plain, (![A_101]: (k9_relat_1(k2_funct_1(A_101), k2_relat_1(A_101))=k1_relat_1(A_101) | ~r1_tarski(k1_relat_1(A_101), k1_relat_1(A_101)) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101) | ~v1_relat_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_485, c_591])).
% 10.93/4.39  tff(c_619, plain, (![A_101]: (k9_relat_1(k2_funct_1(A_101), k2_relat_1(A_101))=k1_relat_1(A_101) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_606])).
% 10.93/4.39  tff(c_6909, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6878, c_619])).
% 10.93/4.39  tff(c_6934, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2994, c_6849, c_6909])).
% 10.93/4.39  tff(c_7115, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_7017, c_24])).
% 10.93/4.39  tff(c_7154, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_7115, c_14])).
% 10.93/4.39  tff(c_7157, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7118, c_7154])).
% 10.93/4.39  tff(c_7189, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7157, c_12])).
% 10.93/4.39  tff(c_7197, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7118, c_6934, c_7189])).
% 10.93/4.39  tff(c_7114, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_7017, c_22])).
% 10.93/4.39  tff(c_7121, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_7114, c_40])).
% 10.93/4.39  tff(c_7124, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7118, c_7121])).
% 10.93/4.39  tff(c_7576, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7109, c_7197, c_7124])).
% 10.93/4.39  tff(c_2993, plain, (~v2_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2937])).
% 10.93/4.39  tff(c_2995, plain, (~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_2993])).
% 10.93/4.39  tff(c_7588, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7576, c_2995])).
% 10.93/4.39  tff(c_7600, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7588])).
% 10.93/4.39  tff(c_7601, plain, (~v2_funct_1(k2_funct_1('#skF_2')) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2993])).
% 10.93/4.39  tff(c_7606, plain, (~v2_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_7601])).
% 10.93/4.39  tff(c_7607, plain, (![A_449, B_450]: (k2_funct_2(A_449, B_450)=k2_funct_1(B_450) | ~m1_subset_1(B_450, k1_zfmisc_1(k2_zfmisc_1(A_449, A_449))) | ~v3_funct_2(B_450, A_449, A_449) | ~v1_funct_2(B_450, A_449, A_449) | ~v1_funct_1(B_450))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_7613, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_7607])).
% 10.93/4.39  tff(c_7617, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_7613])).
% 10.93/4.39  tff(c_7705, plain, (![A_457, B_458]: (v3_funct_2(k2_funct_2(A_457, B_458), A_457, A_457) | ~m1_subset_1(B_458, k1_zfmisc_1(k2_zfmisc_1(A_457, A_457))) | ~v3_funct_2(B_458, A_457, A_457) | ~v1_funct_2(B_458, A_457, A_457) | ~v1_funct_1(B_458))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_7709, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_7705])).
% 10.93/4.39  tff(c_7713, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_7617, c_7709])).
% 10.93/4.39  tff(c_7717, plain, (![A_462, B_463]: (m1_subset_1(k2_funct_2(A_462, B_463), k1_zfmisc_1(k2_zfmisc_1(A_462, A_462))) | ~m1_subset_1(B_463, k1_zfmisc_1(k2_zfmisc_1(A_462, A_462))) | ~v3_funct_2(B_463, A_462, A_462) | ~v1_funct_2(B_463, A_462, A_462) | ~v1_funct_1(B_463))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_7747, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7617, c_7717])).
% 10.93/4.39  tff(c_7761, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_7747])).
% 10.93/4.39  tff(c_7777, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_7761, c_34])).
% 10.93/4.39  tff(c_7806, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2994, c_7713, c_7777])).
% 10.93/4.39  tff(c_7808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7606, c_7806])).
% 10.93/4.39  tff(c_7810, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_7601])).
% 10.93/4.39  tff(c_7809, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_7601])).
% 10.93/4.39  tff(c_8335, plain, (![A_493, B_494]: (k2_funct_2(A_493, B_494)=k2_funct_1(B_494) | ~m1_subset_1(B_494, k1_zfmisc_1(k2_zfmisc_1(A_493, A_493))) | ~v3_funct_2(B_494, A_493, A_493) | ~v1_funct_2(B_494, A_493, A_493) | ~v1_funct_1(B_494))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_8341, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_8335])).
% 10.93/4.39  tff(c_8345, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_8341])).
% 10.93/4.39  tff(c_8930, plain, (![A_523, B_524]: (m1_subset_1(k2_funct_2(A_523, B_524), k1_zfmisc_1(k2_zfmisc_1(A_523, A_523))) | ~m1_subset_1(B_524, k1_zfmisc_1(k2_zfmisc_1(A_523, A_523))) | ~v3_funct_2(B_524, A_523, A_523) | ~v1_funct_2(B_524, A_523, A_523) | ~v1_funct_1(B_524))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_8960, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8345, c_8930])).
% 10.93/4.39  tff(c_8974, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_8960])).
% 10.93/4.39  tff(c_9022, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8974, c_24])).
% 10.93/4.39  tff(c_9034, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_9022, c_14])).
% 10.93/4.39  tff(c_9037, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_9034])).
% 10.93/4.39  tff(c_7866, plain, (![A_466, B_467]: (k2_funct_2(A_466, B_467)=k2_funct_1(B_467) | ~m1_subset_1(B_467, k1_zfmisc_1(k2_zfmisc_1(A_466, A_466))) | ~v3_funct_2(B_467, A_466, A_466) | ~v1_funct_2(B_467, A_466, A_466) | ~v1_funct_1(B_467))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_7872, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_7866])).
% 10.93/4.39  tff(c_7876, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_7872])).
% 10.93/4.39  tff(c_8214, plain, (![A_491, B_492]: (m1_subset_1(k2_funct_2(A_491, B_492), k1_zfmisc_1(k2_zfmisc_1(A_491, A_491))) | ~m1_subset_1(B_492, k1_zfmisc_1(k2_zfmisc_1(A_491, A_491))) | ~v3_funct_2(B_492, A_491, A_491) | ~v1_funct_2(B_492, A_491, A_491) | ~v1_funct_1(B_492))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_8244, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7876, c_8214])).
% 10.93/4.39  tff(c_8258, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_8244])).
% 10.93/4.39  tff(c_8306, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8258, c_24])).
% 10.93/4.39  tff(c_8318, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_8306, c_14])).
% 10.93/4.39  tff(c_8321, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_8318])).
% 10.93/4.39  tff(c_7821, plain, (~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_2901])).
% 10.93/4.39  tff(c_8328, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8321, c_7821])).
% 10.93/4.39  tff(c_8331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2847, c_8328])).
% 10.93/4.39  tff(c_8333, plain, (v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_2901])).
% 10.93/4.39  tff(c_8597, plain, (![A_515, B_516]: (m1_subset_1(k2_funct_2(A_515, B_516), k1_zfmisc_1(k2_zfmisc_1(A_515, A_515))) | ~m1_subset_1(B_516, k1_zfmisc_1(k2_zfmisc_1(A_515, A_515))) | ~v3_funct_2(B_516, A_515, A_515) | ~v1_funct_2(B_516, A_515, A_515) | ~v1_funct_1(B_516))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.93/4.39  tff(c_8627, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8345, c_8597])).
% 10.93/4.39  tff(c_8641, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_8627])).
% 10.93/4.39  tff(c_8689, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_8641, c_24])).
% 10.93/4.39  tff(c_8701, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_8689, c_14])).
% 10.93/4.39  tff(c_8704, plain, (k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_8701])).
% 10.93/4.39  tff(c_8332, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_2901])).
% 10.93/4.39  tff(c_8353, plain, (~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitLeft, [status(thm)], [c_8332])).
% 10.93/4.39  tff(c_8711, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8704, c_8353])).
% 10.93/4.39  tff(c_8715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2994, c_8711])).
% 10.93/4.39  tff(c_8716, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_8332])).
% 10.93/4.39  tff(c_8720, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_8716, c_40])).
% 10.93/4.39  tff(c_8723, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1' | ~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8333, c_8720])).
% 10.93/4.39  tff(c_8733, plain, (~v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_8723])).
% 10.93/4.39  tff(c_8717, plain, (v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))), inference(splitRight, [status(thm)], [c_8332])).
% 10.93/4.39  tff(c_8734, plain, (![B_519, A_520]: (v2_funct_2(k7_relat_1(B_519, A_520), k9_relat_1(B_519, A_520)) | ~v1_funct_1(k7_relat_1(B_519, A_520)) | ~v1_relat_1(k7_relat_1(B_519, A_520)) | ~v1_relat_1(B_519))), inference(superposition, [status(thm), theory('equality')], [c_12, c_467])).
% 10.93/4.39  tff(c_8743, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1') | ~v1_funct_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_8734])).
% 10.93/4.39  tff(c_8766, plain, (v2_funct_2(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_8333, c_8717, c_8743])).
% 10.93/4.39  tff(c_8768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8733, c_8766])).
% 10.93/4.39  tff(c_8769, plain, (k2_relat_1(k7_relat_1(k2_funct_1('#skF_2'), '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_8723])).
% 10.93/4.39  tff(c_9051, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9037, c_8769])).
% 10.93/4.39  tff(c_9076, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9051, c_619])).
% 10.93/4.39  tff(c_9101, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2994, c_7810, c_7809, c_9076])).
% 10.93/4.39  tff(c_7602, plain, (r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_2993])).
% 10.93/4.39  tff(c_7605, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_7602, c_2])).
% 10.93/4.39  tff(c_8334, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_7605])).
% 10.93/4.39  tff(c_9138, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9101, c_8334])).
% 10.93/4.39  tff(c_9142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9138])).
% 10.93/4.39  tff(c_9143, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_7605])).
% 10.93/4.39  tff(c_9150, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9143, c_485])).
% 10.93/4.39  tff(c_9172, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2994, c_2847, c_2442, c_9150])).
% 10.93/4.39  tff(c_56, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_155])).
% 10.93/4.39  tff(c_10232, plain, (![C_569, D_564, F_568, B_565, E_566, A_567]: (k1_partfun1(A_567, B_565, C_569, D_564, E_566, F_568)=k5_relat_1(E_566, F_568) | ~m1_subset_1(F_568, k1_zfmisc_1(k2_zfmisc_1(C_569, D_564))) | ~v1_funct_1(F_568) | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(A_567, B_565))) | ~v1_funct_1(E_566))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.93/4.39  tff(c_11877, plain, (![A_600, B_601, A_602, E_603]: (k1_partfun1(A_600, B_601, k1_relat_1(A_602), k2_relat_1(A_602), E_603, A_602)=k5_relat_1(E_603, A_602) | ~m1_subset_1(E_603, k1_zfmisc_1(k2_zfmisc_1(A_600, B_601))) | ~v1_funct_1(E_603) | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(resolution, [status(thm)], [c_56, c_10232])).
% 10.93/4.39  tff(c_11897, plain, (![A_602]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_602), k2_relat_1(A_602), '#skF_2', A_602)=k5_relat_1('#skF_2', A_602) | ~v1_funct_1('#skF_2') | ~v1_funct_1(A_602) | ~v1_relat_1(A_602))), inference(resolution, [status(thm)], [c_64, c_11877])).
% 10.93/4.39  tff(c_11921, plain, (![A_604]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_604), k2_relat_1(A_604), '#skF_2', A_604)=k5_relat_1('#skF_2', A_604) | ~v1_funct_1(A_604) | ~v1_relat_1(A_604))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_11897])).
% 10.93/4.39  tff(c_11948, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', k2_relat_1(k2_funct_1('#skF_2')), '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9143, c_11921])).
% 10.93/4.39  tff(c_11973, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2994, c_9172, c_11948])).
% 10.93/4.39  tff(c_9245, plain, (![A_531, B_532]: (k2_funct_2(A_531, B_532)=k2_funct_1(B_532) | ~m1_subset_1(B_532, k1_zfmisc_1(k2_zfmisc_1(A_531, A_531))) | ~v3_funct_2(B_532, A_531, A_531) | ~v1_funct_2(B_532, A_531, A_531) | ~v1_funct_1(B_532))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.39  tff(c_9251, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_9245])).
% 10.93/4.39  tff(c_9255, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_9251])).
% 10.93/4.39  tff(c_62, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 10.93/4.39  tff(c_100, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_62])).
% 10.93/4.39  tff(c_9257, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9255, c_100])).
% 10.93/4.39  tff(c_11978, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11973, c_9257])).
% 10.93/4.39  tff(c_11985, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_11978])).
% 10.93/4.39  tff(c_11988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_520, c_369, c_2417, c_11985])).
% 10.93/4.39  tff(c_11989, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_62])).
% 10.93/4.39  tff(c_19166, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19162, c_11989])).
% 10.93/4.39  tff(c_20126, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20012, c_19166])).
% 10.93/4.39  tff(c_20139, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_20126])).
% 10.93/4.39  tff(c_20142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_70, c_12372, c_12253, c_12226, c_20139])).
% 10.93/4.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.93/4.39  
% 10.93/4.39  Inference rules
% 10.93/4.39  ----------------------
% 10.93/4.39  #Ref     : 0
% 10.93/4.39  #Sup     : 4223
% 10.93/4.39  #Fact    : 0
% 10.93/4.39  #Define  : 0
% 10.93/4.39  #Split   : 83
% 10.93/4.39  #Chain   : 0
% 10.93/4.39  #Close   : 0
% 10.93/4.39  
% 10.93/4.39  Ordering : KBO
% 10.93/4.39  
% 10.93/4.39  Simplification rules
% 10.93/4.39  ----------------------
% 10.93/4.39  #Subsume      : 301
% 10.93/4.39  #Demod        : 9510
% 10.93/4.39  #Tautology    : 1513
% 10.93/4.39  #SimpNegUnit  : 25
% 10.93/4.39  #BackRed      : 433
% 10.93/4.39  
% 10.93/4.39  #Partial instantiations: 0
% 10.93/4.39  #Strategies tried      : 1
% 10.93/4.39  
% 10.93/4.39  Timing (in seconds)
% 10.93/4.39  ----------------------
% 10.93/4.39  Preprocessing        : 0.35
% 10.93/4.39  Parsing              : 0.18
% 10.93/4.39  CNF conversion       : 0.02
% 10.93/4.39  Main loop            : 3.10
% 10.93/4.39  Inferencing          : 1.00
% 10.93/4.39  Reduction            : 1.28
% 10.93/4.39  Demodulation         : 0.98
% 10.93/4.39  BG Simplification    : 0.09
% 10.93/4.39  Subsumption          : 0.52
% 10.93/4.39  Abstraction          : 0.12
% 10.93/4.39  MUC search           : 0.00
% 10.93/4.39  Cooper               : 0.00
% 10.93/4.39  Total                : 3.68
% 10.93/4.39  Index Insertion      : 0.00
% 10.93/4.39  Index Deletion       : 0.00
% 10.93/4.39  Index Matching       : 0.00
% 10.93/4.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
