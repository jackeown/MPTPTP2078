%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:10 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  228 (14448 expanded)
%              Number of leaves         :   46 (4631 expanded)
%              Depth                    :   24
%              Number of atoms          :  495 (31876 expanded)
%              Number of equality atoms :  134 (10364 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_34,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_65,axiom,(
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

tff(f_59,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_37,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_74,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_133,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_133])).

tff(c_145,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_139])).

tff(c_80,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_76,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4688,plain,(
    ! [C_464,A_465,B_466] :
      ( v2_funct_1(C_464)
      | ~ v3_funct_2(C_464,A_465,B_466)
      | ~ v1_funct_1(C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_465,B_466))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4697,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_4688])).

tff(c_4702,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_4697])).

tff(c_64,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4562,plain,(
    ! [A_444,B_445,D_446] :
      ( r2_relset_1(A_444,B_445,D_446,D_446)
      | ~ m1_subset_1(D_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4570,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_64,c_4562])).

tff(c_146,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_146])).

tff(c_4330,plain,(
    ! [B_406,A_407] :
      ( k2_relat_1(B_406) = A_407
      | ~ v2_funct_2(B_406,A_407)
      | ~ v5_relat_1(B_406,A_407)
      | ~ v1_relat_1(B_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4339,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_4330])).

tff(c_4348,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_4339])).

tff(c_4349,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4348])).

tff(c_4529,plain,(
    ! [C_439,B_440,A_441] :
      ( v2_funct_2(C_439,B_440)
      | ~ v3_funct_2(C_439,A_441,B_440)
      | ~ v1_funct_1(C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_441,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4538,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_4529])).

tff(c_4544,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_4538])).

tff(c_4546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4349,c_4544])).

tff(c_4547,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4348])).

tff(c_70,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_18,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_partfun1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18])).

tff(c_78,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4861,plain,(
    ! [A_491,B_492] :
      ( k2_funct_2(A_491,B_492) = k2_funct_1(B_492)
      | ~ m1_subset_1(B_492,k1_zfmisc_1(k2_zfmisc_1(A_491,A_491)))
      | ~ v3_funct_2(B_492,A_491,A_491)
      | ~ v1_funct_2(B_492,A_491,A_491)
      | ~ v1_funct_1(B_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4870,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_4861])).

tff(c_4875,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_4870])).

tff(c_4836,plain,(
    ! [A_487,B_488] :
      ( v1_funct_1(k2_funct_2(A_487,B_488))
      | ~ m1_subset_1(B_488,k1_zfmisc_1(k2_zfmisc_1(A_487,A_487)))
      | ~ v3_funct_2(B_488,A_487,A_487)
      | ~ v1_funct_2(B_488,A_487,A_487)
      | ~ v1_funct_1(B_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4845,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_4836])).

tff(c_4850,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_4845])).

tff(c_4876,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4875,c_4850])).

tff(c_54,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k2_funct_2(A_27,B_28),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k2_zfmisc_1(A_27,A_27)))
      | ~ v3_funct_2(B_28,A_27,A_27)
      | ~ v1_funct_2(B_28,A_27,A_27)
      | ~ v1_funct_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5123,plain,(
    ! [E_512,A_511,F_510,D_513,C_508,B_509] :
      ( k1_partfun1(A_511,B_509,C_508,D_513,E_512,F_510) = k5_relat_1(E_512,F_510)
      | ~ m1_subset_1(F_510,k1_zfmisc_1(k2_zfmisc_1(C_508,D_513)))
      | ~ v1_funct_1(F_510)
      | ~ m1_subset_1(E_512,k1_zfmisc_1(k2_zfmisc_1(A_511,B_509)))
      | ~ v1_funct_1(E_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5133,plain,(
    ! [A_511,B_509,E_512] :
      ( k1_partfun1(A_511,B_509,'#skF_1','#skF_1',E_512,'#skF_2') = k5_relat_1(E_512,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_512,k1_zfmisc_1(k2_zfmisc_1(A_511,B_509)))
      | ~ v1_funct_1(E_512) ) ),
    inference(resolution,[status(thm)],[c_74,c_5123])).

tff(c_5155,plain,(
    ! [A_514,B_515,E_516] :
      ( k1_partfun1(A_514,B_515,'#skF_1','#skF_1',E_516,'#skF_2') = k5_relat_1(E_516,'#skF_2')
      | ~ m1_subset_1(E_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515)))
      | ~ v1_funct_1(E_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5133])).

tff(c_5421,plain,(
    ! [A_524,B_525] :
      ( k1_partfun1(A_524,A_524,'#skF_1','#skF_1',k2_funct_2(A_524,B_525),'#skF_2') = k5_relat_1(k2_funct_2(A_524,B_525),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_524,B_525))
      | ~ m1_subset_1(B_525,k1_zfmisc_1(k2_zfmisc_1(A_524,A_524)))
      | ~ v3_funct_2(B_525,A_524,A_524)
      | ~ v1_funct_2(B_525,A_524,A_524)
      | ~ v1_funct_1(B_525) ) ),
    inference(resolution,[status(thm)],[c_54,c_5155])).

tff(c_5433,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_5421])).

tff(c_5445,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_4876,c_4875,c_4875,c_4875,c_5433])).

tff(c_594,plain,(
    ! [C_115,A_116,B_117] :
      ( v2_funct_1(C_115)
      | ~ v3_funct_2(C_115,A_116,B_117)
      | ~ v1_funct_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_603,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_594])).

tff(c_608,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_603])).

tff(c_295,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_303,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_64,c_295])).

tff(c_14,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_136,plain,(
    ! [A_29] :
      ( v1_relat_1(k6_partfun1(A_29))
      | ~ v1_relat_1(k2_zfmisc_1(A_29,A_29)) ) ),
    inference(resolution,[status(thm)],[c_64,c_133])).

tff(c_163,plain,(
    ! [A_53] : v1_relat_1(k6_partfun1(A_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_136])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [A_53] :
      ( k1_relat_1(k6_partfun1(A_53)) != k1_xboole_0
      | k6_partfun1(A_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_163,c_12])).

tff(c_171,plain,(
    ! [A_53] :
      ( k1_xboole_0 != A_53
      | k6_partfun1(A_53) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_166])).

tff(c_72,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_174,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_222,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_174])).

tff(c_271,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_518,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_532,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_518])).

tff(c_686,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_695,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_686])).

tff(c_701,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_532,c_695])).

tff(c_702,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_701])).

tff(c_20,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_20])).

tff(c_792,plain,(
    ! [A_146,B_147] :
      ( k2_funct_2(A_146,B_147) = k2_funct_1(B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(k2_zfmisc_1(A_146,A_146)))
      | ~ v3_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_2(B_147,A_146,A_146)
      | ~ v1_funct_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_801,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_792])).

tff(c_806,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_801])).

tff(c_762,plain,(
    ! [A_141,B_142] :
      ( v1_funct_1(k2_funct_2(A_141,B_142))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v3_funct_2(B_142,A_141,A_141)
      | ~ v1_funct_2(B_142,A_141,A_141)
      | ~ v1_funct_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_771,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_762])).

tff(c_776,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_771])).

tff(c_807,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_776])).

tff(c_1030,plain,(
    ! [C_158,E_162,B_159,A_161,D_163,F_160] :
      ( k1_partfun1(A_161,B_159,C_158,D_163,E_162,F_160) = k5_relat_1(E_162,F_160)
      | ~ m1_subset_1(F_160,k1_zfmisc_1(k2_zfmisc_1(C_158,D_163)))
      | ~ v1_funct_1(F_160)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_159)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2395,plain,(
    ! [A_202,B_204,A_206,B_205,E_203] :
      ( k1_partfun1(A_202,B_204,A_206,A_206,E_203,k2_funct_2(A_206,B_205)) = k5_relat_1(E_203,k2_funct_2(A_206,B_205))
      | ~ v1_funct_1(k2_funct_2(A_206,B_205))
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_202,B_204)))
      | ~ v1_funct_1(E_203)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_205,A_206,A_206)
      | ~ v1_funct_2(B_205,A_206,A_206)
      | ~ v1_funct_1(B_205) ) ),
    inference(resolution,[status(thm)],[c_54,c_1030])).

tff(c_2413,plain,(
    ! [A_206,B_205] :
      ( k1_partfun1('#skF_1','#skF_1',A_206,A_206,'#skF_2',k2_funct_2(A_206,B_205)) = k5_relat_1('#skF_2',k2_funct_2(A_206,B_205))
      | ~ v1_funct_1(k2_funct_2(A_206,B_205))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_205,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_205,A_206,A_206)
      | ~ v1_funct_2(B_205,A_206,A_206)
      | ~ v1_funct_1(B_205) ) ),
    inference(resolution,[status(thm)],[c_74,c_2395])).

tff(c_2443,plain,(
    ! [A_207,B_208] :
      ( k1_partfun1('#skF_1','#skF_1',A_207,A_207,'#skF_2',k2_funct_2(A_207,B_208)) = k5_relat_1('#skF_2',k2_funct_2(A_207,B_208))
      | ~ v1_funct_1(k2_funct_2(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2413])).

tff(c_2461,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2443])).

tff(c_2482,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_807,c_806,c_806,c_806,c_2461])).

tff(c_808,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_174])).

tff(c_2496,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2482,c_808])).

tff(c_2503,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2496])).

tff(c_2509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_80,c_608,c_303,c_702,c_2503])).

tff(c_2511,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_161,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_145,c_12])).

tff(c_176,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_2518,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_176])).

tff(c_2704,plain,(
    ! [A_225,B_226,C_227] :
      ( k1_relset_1(A_225,B_226,C_227) = k1_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2718,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2704])).

tff(c_46,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2861,plain,(
    ! [B_249,C_250] :
      ( k1_relset_1('#skF_1',B_249,C_250) = '#skF_1'
      | ~ v1_funct_2(C_250,'#skF_1',B_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_249))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_2511,c_2511,c_2511,c_46])).

tff(c_2872,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_2861])).

tff(c_2881,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2718,c_2872])).

tff(c_2883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2518,c_2881])).

tff(c_2884,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_2916,plain,(
    ! [A_53] :
      ( A_53 != '#skF_2'
      | k6_partfun1(A_53) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2884,c_171])).

tff(c_2952,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2916,c_174])).

tff(c_3000,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2952])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2888,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2884,c_6])).

tff(c_3039,plain,(
    ! [B_267,A_268] :
      ( k2_relat_1(B_267) = A_268
      | ~ v2_funct_2(B_267,A_268)
      | ~ v5_relat_1(B_267,A_268)
      | ~ v1_relat_1(B_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3048,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_3039])).

tff(c_3057,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_2888,c_3048])).

tff(c_3058,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3000,c_3057])).

tff(c_3234,plain,(
    ! [C_294,B_295,A_296] :
      ( v2_funct_2(C_294,B_295)
      | ~ v3_funct_2(C_294,A_296,B_295)
      | ~ v1_funct_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_296,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3243,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_3234])).

tff(c_3251,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3243])).

tff(c_3253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3058,c_3251])).

tff(c_3255,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2952])).

tff(c_2918,plain,(
    ! [A_255] :
      ( A_255 != '#skF_2'
      | k6_partfun1(A_255) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2884,c_171])).

tff(c_2932,plain,(
    ! [A_255] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_255,A_255)))
      | A_255 != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2918,c_64])).

tff(c_3446,plain,(
    ! [A_311] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_311,A_311)))
      | A_311 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_2932])).

tff(c_28,plain,(
    ! [A_15,B_16,D_18] :
      ( r2_relset_1(A_15,B_16,D_18,D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3471,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3446,c_28])).

tff(c_3272,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_80])).

tff(c_3268,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_145])).

tff(c_3443,plain,(
    ! [A_255] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_255,A_255)))
      | A_255 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_2932])).

tff(c_3557,plain,(
    ! [C_327,A_328,B_329] :
      ( v2_funct_1(C_327)
      | ~ v3_funct_2(C_327,A_328,B_329)
      | ~ v1_funct_1(C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3560,plain,(
    ! [A_255] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_1('#skF_1')
      | A_255 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3443,c_3557])).

tff(c_3566,plain,(
    ! [A_255] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_255,A_255)
      | A_255 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3560])).

tff(c_3587,plain,(
    ~ v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3566])).

tff(c_3270,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_76])).

tff(c_3589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3587,c_3270])).

tff(c_3590,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3566])).

tff(c_3308,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_2916])).

tff(c_2885,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_2894,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2885])).

tff(c_3265,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_2894])).

tff(c_3271,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_78])).

tff(c_3712,plain,(
    ! [A_355,B_356] :
      ( k2_funct_2(A_355,B_356) = k2_funct_1(B_356)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(k2_zfmisc_1(A_355,A_355)))
      | ~ v3_funct_2(B_356,A_355,A_355)
      | ~ v1_funct_2(B_356,A_355,A_355)
      | ~ v1_funct_1(B_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3715,plain,(
    ! [A_255] :
      ( k2_funct_2(A_255,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_1('#skF_1')
      | A_255 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3443,c_3712])).

tff(c_3724,plain,(
    ! [A_357] :
      ( k2_funct_2(A_357,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_357,A_357)
      | ~ v1_funct_2('#skF_1',A_357,A_357)
      | A_357 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3715])).

tff(c_3727,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3270,c_3724])).

tff(c_3730,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3727])).

tff(c_3765,plain,(
    ! [A_363,B_364] :
      ( v1_funct_2(k2_funct_2(A_363,B_364),A_363,A_363)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(k2_zfmisc_1(A_363,A_363)))
      | ~ v3_funct_2(B_364,A_363,A_363)
      | ~ v1_funct_2(B_364,A_363,A_363)
      | ~ v1_funct_1(B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3767,plain,(
    ! [A_255] :
      ( v1_funct_2(k2_funct_2(A_255,'#skF_1'),A_255,A_255)
      | ~ v3_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_1('#skF_1')
      | A_255 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3443,c_3765])).

tff(c_3775,plain,(
    ! [A_365] :
      ( v1_funct_2(k2_funct_2(A_365,'#skF_1'),A_365,A_365)
      | ~ v3_funct_2('#skF_1',A_365,A_365)
      | ~ v1_funct_2('#skF_1',A_365,A_365)
      | A_365 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3767])).

tff(c_3778,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3730,c_3775])).

tff(c_3781,plain,(
    v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3270,c_3778])).

tff(c_3444,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_2932])).

tff(c_3820,plain,(
    ! [A_373,B_374] :
      ( m1_subset_1(k2_funct_2(A_373,B_374),k1_zfmisc_1(k2_zfmisc_1(A_373,A_373)))
      | ~ m1_subset_1(B_374,k1_zfmisc_1(k2_zfmisc_1(A_373,A_373)))
      | ~ v3_funct_2(B_374,A_373,A_373)
      | ~ v1_funct_2(B_374,A_373,A_373)
      | ~ v1_funct_1(B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3871,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3730,c_3820])).

tff(c_3892,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3271,c_3270,c_3444,c_3871])).

tff(c_3266,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_2884])).

tff(c_3602,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1('#skF_1',B_23,C_24) = '#skF_1'
      | ~ v1_funct_2(C_24,'#skF_1',B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_23))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3266,c_3266,c_3266,c_3266,c_46])).

tff(c_3917,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3892,c_3602])).

tff(c_3964,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3781,c_3917])).

tff(c_26,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3972,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3892,c_26])).

tff(c_4032,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3964,c_3972])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3937,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3892,c_2])).

tff(c_3978,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_3937])).

tff(c_2886,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != '#skF_2'
      | A_6 = '#skF_2'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_2884,c_12])).

tff(c_3257,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != '#skF_1'
      | A_6 = '#skF_1'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_2886])).

tff(c_3985,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3978,c_3257])).

tff(c_4038,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4032,c_3985])).

tff(c_4079,plain,
    ( k6_partfun1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4038,c_81])).

tff(c_4085,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3268,c_3272,c_3590,c_3308,c_3265,c_4079])).

tff(c_3694,plain,(
    ! [A_352,B_353] :
      ( v1_funct_1(k2_funct_2(A_352,B_353))
      | ~ m1_subset_1(B_353,k1_zfmisc_1(k2_zfmisc_1(A_352,A_352)))
      | ~ v3_funct_2(B_353,A_352,A_352)
      | ~ v1_funct_2(B_353,A_352,A_352)
      | ~ v1_funct_1(B_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3697,plain,(
    ! [A_255] :
      ( v1_funct_1(k2_funct_2(A_255,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_2('#skF_1',A_255,A_255)
      | ~ v1_funct_1('#skF_1')
      | A_255 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3443,c_3694])).

tff(c_3706,plain,(
    ! [A_354] :
      ( v1_funct_1(k2_funct_2(A_354,'#skF_1'))
      | ~ v3_funct_2('#skF_1',A_354,A_354)
      | ~ v1_funct_2('#skF_1',A_354,A_354)
      | A_354 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3697])).

tff(c_3708,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3270,c_3706])).

tff(c_3711,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3708])).

tff(c_3731,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_3711])).

tff(c_3997,plain,(
    ! [C_375,E_379,F_377,A_378,D_380,B_376] :
      ( k1_partfun1(A_378,B_376,C_375,D_380,E_379,F_377) = k5_relat_1(E_379,F_377)
      | ~ m1_subset_1(F_377,k1_zfmisc_1(k2_zfmisc_1(C_375,D_380)))
      | ~ v1_funct_1(F_377)
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(A_378,B_376)))
      | ~ v1_funct_1(E_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3999,plain,(
    ! [A_378,B_376,E_379] :
      ( k1_partfun1(A_378,B_376,'#skF_1','#skF_1',E_379,k2_funct_1('#skF_1')) = k5_relat_1(E_379,k2_funct_1('#skF_1'))
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(A_378,B_376)))
      | ~ v1_funct_1(E_379) ) ),
    inference(resolution,[status(thm)],[c_3892,c_3997])).

tff(c_4008,plain,(
    ! [A_378,B_376,E_379] :
      ( k1_partfun1(A_378,B_376,'#skF_1','#skF_1',E_379,k2_funct_1('#skF_1')) = k5_relat_1(E_379,k2_funct_1('#skF_1'))
      | ~ m1_subset_1(E_379,k1_zfmisc_1(k2_zfmisc_1(A_378,B_376)))
      | ~ v1_funct_1(E_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3731,c_3999])).

tff(c_4186,plain,(
    ! [A_390,B_391,E_392] :
      ( k1_partfun1(A_390,B_391,'#skF_1','#skF_1',E_392,'#skF_1') = k5_relat_1(E_392,'#skF_1')
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391)))
      | ~ v1_funct_1(E_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4038,c_4038,c_4008])).

tff(c_4192,plain,(
    ! [A_255] :
      ( k1_partfun1(A_255,A_255,'#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_255 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3443,c_4186])).

tff(c_4201,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_4085,c_4192])).

tff(c_3261,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_3255,c_174])).

tff(c_3425,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3308,c_3261])).

tff(c_3732,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_3425])).

tff(c_4054,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4038,c_3732])).

tff(c_4202,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4201,c_4054])).

tff(c_4205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3471,c_4202])).

tff(c_4206,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_4879,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4875,c_4206])).

tff(c_5480,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5445,c_4879])).

tff(c_5487,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_5480])).

tff(c_5493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_80,c_4702,c_4570,c_4547,c_5487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:38:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.44  
% 7.32/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.45  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.32/2.45  
% 7.32/2.45  %Foreground sorts:
% 7.32/2.45  
% 7.32/2.45  
% 7.32/2.45  %Background operators:
% 7.32/2.45  
% 7.32/2.45  
% 7.32/2.45  %Foreground operators:
% 7.32/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.32/2.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.32/2.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.32/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.32/2.45  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.32/2.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.32/2.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.32/2.45  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.32/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.32/2.45  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.32/2.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.32/2.45  tff('#skF_2', type, '#skF_2': $i).
% 7.32/2.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.32/2.45  tff('#skF_1', type, '#skF_1': $i).
% 7.32/2.45  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.32/2.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.32/2.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.32/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.32/2.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.32/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.32/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.32/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.32/2.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.32/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.32/2.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.32/2.45  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.32/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.32/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.32/2.45  
% 7.32/2.48  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.32/2.48  tff(f_170, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 7.32/2.48  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.32/2.48  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.32/2.48  tff(f_135, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.32/2.48  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.32/2.48  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.32/2.48  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.32/2.48  tff(f_157, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.32/2.48  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.32/2.48  tff(f_155, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.32/2.48  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.32/2.48  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.32/2.48  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.32/2.48  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.32/2.48  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.32/2.48  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.32/2.48  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.32/2.48  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.32/2.48  tff(c_74, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.32/2.48  tff(c_133, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.32/2.48  tff(c_139, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_133])).
% 7.32/2.48  tff(c_145, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_139])).
% 7.32/2.48  tff(c_80, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.32/2.48  tff(c_76, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.32/2.48  tff(c_4688, plain, (![C_464, A_465, B_466]: (v2_funct_1(C_464) | ~v3_funct_2(C_464, A_465, B_466) | ~v1_funct_1(C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_465, B_466))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.32/2.48  tff(c_4697, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_4688])).
% 7.32/2.48  tff(c_4702, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_4697])).
% 7.32/2.48  tff(c_64, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.32/2.48  tff(c_4562, plain, (![A_444, B_445, D_446]: (r2_relset_1(A_444, B_445, D_446, D_446) | ~m1_subset_1(D_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.32/2.48  tff(c_4570, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_64, c_4562])).
% 7.32/2.48  tff(c_146, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.32/2.48  tff(c_154, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_146])).
% 7.32/2.48  tff(c_4330, plain, (![B_406, A_407]: (k2_relat_1(B_406)=A_407 | ~v2_funct_2(B_406, A_407) | ~v5_relat_1(B_406, A_407) | ~v1_relat_1(B_406))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.32/2.48  tff(c_4339, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_4330])).
% 7.32/2.48  tff(c_4348, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_4339])).
% 7.32/2.48  tff(c_4349, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4348])).
% 7.32/2.48  tff(c_4529, plain, (![C_439, B_440, A_441]: (v2_funct_2(C_439, B_440) | ~v3_funct_2(C_439, A_441, B_440) | ~v1_funct_1(C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_441, B_440))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.32/2.48  tff(c_4538, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_4529])).
% 7.32/2.48  tff(c_4544, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_4538])).
% 7.32/2.48  tff(c_4546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4349, c_4544])).
% 7.32/2.48  tff(c_4547, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4348])).
% 7.32/2.48  tff(c_70, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.32/2.48  tff(c_18, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.32/2.48  tff(c_82, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_partfun1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18])).
% 7.32/2.48  tff(c_78, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.32/2.48  tff(c_4861, plain, (![A_491, B_492]: (k2_funct_2(A_491, B_492)=k2_funct_1(B_492) | ~m1_subset_1(B_492, k1_zfmisc_1(k2_zfmisc_1(A_491, A_491))) | ~v3_funct_2(B_492, A_491, A_491) | ~v1_funct_2(B_492, A_491, A_491) | ~v1_funct_1(B_492))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.32/2.48  tff(c_4870, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_4861])).
% 7.32/2.48  tff(c_4875, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_4870])).
% 7.32/2.48  tff(c_4836, plain, (![A_487, B_488]: (v1_funct_1(k2_funct_2(A_487, B_488)) | ~m1_subset_1(B_488, k1_zfmisc_1(k2_zfmisc_1(A_487, A_487))) | ~v3_funct_2(B_488, A_487, A_487) | ~v1_funct_2(B_488, A_487, A_487) | ~v1_funct_1(B_488))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.32/2.48  tff(c_4845, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_4836])).
% 7.32/2.48  tff(c_4850, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_4845])).
% 7.32/2.48  tff(c_4876, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4875, c_4850])).
% 7.32/2.48  tff(c_54, plain, (![A_27, B_28]: (m1_subset_1(k2_funct_2(A_27, B_28), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))) | ~m1_subset_1(B_28, k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))) | ~v3_funct_2(B_28, A_27, A_27) | ~v1_funct_2(B_28, A_27, A_27) | ~v1_funct_1(B_28))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.32/2.48  tff(c_5123, plain, (![E_512, A_511, F_510, D_513, C_508, B_509]: (k1_partfun1(A_511, B_509, C_508, D_513, E_512, F_510)=k5_relat_1(E_512, F_510) | ~m1_subset_1(F_510, k1_zfmisc_1(k2_zfmisc_1(C_508, D_513))) | ~v1_funct_1(F_510) | ~m1_subset_1(E_512, k1_zfmisc_1(k2_zfmisc_1(A_511, B_509))) | ~v1_funct_1(E_512))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.32/2.48  tff(c_5133, plain, (![A_511, B_509, E_512]: (k1_partfun1(A_511, B_509, '#skF_1', '#skF_1', E_512, '#skF_2')=k5_relat_1(E_512, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_512, k1_zfmisc_1(k2_zfmisc_1(A_511, B_509))) | ~v1_funct_1(E_512))), inference(resolution, [status(thm)], [c_74, c_5123])).
% 7.32/2.48  tff(c_5155, plain, (![A_514, B_515, E_516]: (k1_partfun1(A_514, B_515, '#skF_1', '#skF_1', E_516, '#skF_2')=k5_relat_1(E_516, '#skF_2') | ~m1_subset_1(E_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))) | ~v1_funct_1(E_516))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5133])).
% 7.32/2.48  tff(c_5421, plain, (![A_524, B_525]: (k1_partfun1(A_524, A_524, '#skF_1', '#skF_1', k2_funct_2(A_524, B_525), '#skF_2')=k5_relat_1(k2_funct_2(A_524, B_525), '#skF_2') | ~v1_funct_1(k2_funct_2(A_524, B_525)) | ~m1_subset_1(B_525, k1_zfmisc_1(k2_zfmisc_1(A_524, A_524))) | ~v3_funct_2(B_525, A_524, A_524) | ~v1_funct_2(B_525, A_524, A_524) | ~v1_funct_1(B_525))), inference(resolution, [status(thm)], [c_54, c_5155])).
% 7.32/2.48  tff(c_5433, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_5421])).
% 7.32/2.48  tff(c_5445, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_4876, c_4875, c_4875, c_4875, c_5433])).
% 7.32/2.48  tff(c_594, plain, (![C_115, A_116, B_117]: (v2_funct_1(C_115) | ~v3_funct_2(C_115, A_116, B_117) | ~v1_funct_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.32/2.48  tff(c_603, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_594])).
% 7.32/2.48  tff(c_608, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_603])).
% 7.32/2.48  tff(c_295, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.32/2.48  tff(c_303, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_64, c_295])).
% 7.32/2.48  tff(c_14, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.32/2.48  tff(c_84, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14])).
% 7.32/2.48  tff(c_136, plain, (![A_29]: (v1_relat_1(k6_partfun1(A_29)) | ~v1_relat_1(k2_zfmisc_1(A_29, A_29)))), inference(resolution, [status(thm)], [c_64, c_133])).
% 7.32/2.48  tff(c_163, plain, (![A_53]: (v1_relat_1(k6_partfun1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_136])).
% 7.32/2.48  tff(c_12, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.32/2.48  tff(c_166, plain, (![A_53]: (k1_relat_1(k6_partfun1(A_53))!=k1_xboole_0 | k6_partfun1(A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_163, c_12])).
% 7.32/2.48  tff(c_171, plain, (![A_53]: (k1_xboole_0!=A_53 | k6_partfun1(A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_166])).
% 7.32/2.48  tff(c_72, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.32/2.48  tff(c_174, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_72])).
% 7.32/2.48  tff(c_222, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_171, c_174])).
% 7.32/2.48  tff(c_271, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_222])).
% 7.32/2.48  tff(c_518, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.32/2.48  tff(c_532, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_518])).
% 7.32/2.48  tff(c_686, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.32/2.48  tff(c_695, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_686])).
% 7.32/2.48  tff(c_701, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_532, c_695])).
% 7.32/2.48  tff(c_702, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_271, c_701])).
% 7.32/2.48  tff(c_20, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.32/2.48  tff(c_81, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_20])).
% 7.32/2.48  tff(c_792, plain, (![A_146, B_147]: (k2_funct_2(A_146, B_147)=k2_funct_1(B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(k2_zfmisc_1(A_146, A_146))) | ~v3_funct_2(B_147, A_146, A_146) | ~v1_funct_2(B_147, A_146, A_146) | ~v1_funct_1(B_147))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.32/2.48  tff(c_801, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_792])).
% 7.32/2.48  tff(c_806, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_801])).
% 7.32/2.48  tff(c_762, plain, (![A_141, B_142]: (v1_funct_1(k2_funct_2(A_141, B_142)) | ~m1_subset_1(B_142, k1_zfmisc_1(k2_zfmisc_1(A_141, A_141))) | ~v3_funct_2(B_142, A_141, A_141) | ~v1_funct_2(B_142, A_141, A_141) | ~v1_funct_1(B_142))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.32/2.48  tff(c_771, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_762])).
% 7.32/2.48  tff(c_776, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_771])).
% 7.32/2.48  tff(c_807, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_776])).
% 7.32/2.48  tff(c_1030, plain, (![C_158, E_162, B_159, A_161, D_163, F_160]: (k1_partfun1(A_161, B_159, C_158, D_163, E_162, F_160)=k5_relat_1(E_162, F_160) | ~m1_subset_1(F_160, k1_zfmisc_1(k2_zfmisc_1(C_158, D_163))) | ~v1_funct_1(F_160) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_159))) | ~v1_funct_1(E_162))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.32/2.48  tff(c_2395, plain, (![A_202, B_204, A_206, B_205, E_203]: (k1_partfun1(A_202, B_204, A_206, A_206, E_203, k2_funct_2(A_206, B_205))=k5_relat_1(E_203, k2_funct_2(A_206, B_205)) | ~v1_funct_1(k2_funct_2(A_206, B_205)) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_202, B_204))) | ~v1_funct_1(E_203) | ~m1_subset_1(B_205, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_205, A_206, A_206) | ~v1_funct_2(B_205, A_206, A_206) | ~v1_funct_1(B_205))), inference(resolution, [status(thm)], [c_54, c_1030])).
% 7.32/2.48  tff(c_2413, plain, (![A_206, B_205]: (k1_partfun1('#skF_1', '#skF_1', A_206, A_206, '#skF_2', k2_funct_2(A_206, B_205))=k5_relat_1('#skF_2', k2_funct_2(A_206, B_205)) | ~v1_funct_1(k2_funct_2(A_206, B_205)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_205, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_205, A_206, A_206) | ~v1_funct_2(B_205, A_206, A_206) | ~v1_funct_1(B_205))), inference(resolution, [status(thm)], [c_74, c_2395])).
% 7.32/2.48  tff(c_2443, plain, (![A_207, B_208]: (k1_partfun1('#skF_1', '#skF_1', A_207, A_207, '#skF_2', k2_funct_2(A_207, B_208))=k5_relat_1('#skF_2', k2_funct_2(A_207, B_208)) | ~v1_funct_1(k2_funct_2(A_207, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2413])).
% 7.32/2.48  tff(c_2461, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2443])).
% 7.32/2.48  tff(c_2482, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_807, c_806, c_806, c_806, c_2461])).
% 7.32/2.48  tff(c_808, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_174])).
% 7.32/2.48  tff(c_2496, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2482, c_808])).
% 7.32/2.48  tff(c_2503, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_81, c_2496])).
% 7.32/2.48  tff(c_2509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_80, c_608, c_303, c_702, c_2503])).
% 7.32/2.48  tff(c_2511, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_222])).
% 7.32/2.48  tff(c_161, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_145, c_12])).
% 7.32/2.48  tff(c_176, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_161])).
% 7.32/2.48  tff(c_2518, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_176])).
% 7.32/2.48  tff(c_2704, plain, (![A_225, B_226, C_227]: (k1_relset_1(A_225, B_226, C_227)=k1_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.32/2.48  tff(c_2718, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2704])).
% 7.32/2.48  tff(c_46, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.32/2.48  tff(c_2861, plain, (![B_249, C_250]: (k1_relset_1('#skF_1', B_249, C_250)='#skF_1' | ~v1_funct_2(C_250, '#skF_1', B_249) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_249))))), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_2511, c_2511, c_2511, c_46])).
% 7.32/2.48  tff(c_2872, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_2861])).
% 7.32/2.48  tff(c_2881, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2718, c_2872])).
% 7.32/2.48  tff(c_2883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2518, c_2881])).
% 7.32/2.48  tff(c_2884, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_161])).
% 7.32/2.48  tff(c_2916, plain, (![A_53]: (A_53!='#skF_2' | k6_partfun1(A_53)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2884, c_171])).
% 7.32/2.48  tff(c_2952, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2') | '#skF_2'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2916, c_174])).
% 7.32/2.48  tff(c_3000, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_2952])).
% 7.32/2.48  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.32/2.48  tff(c_2888, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2884, c_6])).
% 7.32/2.48  tff(c_3039, plain, (![B_267, A_268]: (k2_relat_1(B_267)=A_268 | ~v2_funct_2(B_267, A_268) | ~v5_relat_1(B_267, A_268) | ~v1_relat_1(B_267))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.32/2.48  tff(c_3048, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_3039])).
% 7.32/2.48  tff(c_3057, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_2888, c_3048])).
% 7.32/2.48  tff(c_3058, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3000, c_3057])).
% 7.32/2.48  tff(c_3234, plain, (![C_294, B_295, A_296]: (v2_funct_2(C_294, B_295) | ~v3_funct_2(C_294, A_296, B_295) | ~v1_funct_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_296, B_295))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.32/2.48  tff(c_3243, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_3234])).
% 7.32/2.48  tff(c_3251, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3243])).
% 7.32/2.48  tff(c_3253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3058, c_3251])).
% 7.32/2.48  tff(c_3255, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2952])).
% 7.32/2.48  tff(c_2918, plain, (![A_255]: (A_255!='#skF_2' | k6_partfun1(A_255)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2884, c_171])).
% 7.32/2.48  tff(c_2932, plain, (![A_255]: (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_255, A_255))) | A_255!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2918, c_64])).
% 7.32/2.48  tff(c_3446, plain, (![A_311]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_311, A_311))) | A_311!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_2932])).
% 7.32/2.48  tff(c_28, plain, (![A_15, B_16, D_18]: (r2_relset_1(A_15, B_16, D_18, D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.32/2.48  tff(c_3471, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3446, c_28])).
% 7.32/2.48  tff(c_3272, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_80])).
% 7.32/2.48  tff(c_3268, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_145])).
% 7.32/2.48  tff(c_3443, plain, (![A_255]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_255, A_255))) | A_255!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_2932])).
% 7.32/2.48  tff(c_3557, plain, (![C_327, A_328, B_329]: (v2_funct_1(C_327) | ~v3_funct_2(C_327, A_328, B_329) | ~v1_funct_1(C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.32/2.48  tff(c_3560, plain, (![A_255]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_255, A_255) | ~v1_funct_1('#skF_1') | A_255!='#skF_1')), inference(resolution, [status(thm)], [c_3443, c_3557])).
% 7.32/2.48  tff(c_3566, plain, (![A_255]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_255, A_255) | A_255!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3560])).
% 7.32/2.48  tff(c_3587, plain, (~v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3566])).
% 7.32/2.48  tff(c_3270, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_76])).
% 7.32/2.48  tff(c_3589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3587, c_3270])).
% 7.32/2.48  tff(c_3590, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_3566])).
% 7.32/2.48  tff(c_3308, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_2916])).
% 7.32/2.48  tff(c_2885, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_161])).
% 7.32/2.48  tff(c_2894, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2885])).
% 7.32/2.48  tff(c_3265, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_2894])).
% 7.32/2.48  tff(c_3271, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_78])).
% 7.32/2.48  tff(c_3712, plain, (![A_355, B_356]: (k2_funct_2(A_355, B_356)=k2_funct_1(B_356) | ~m1_subset_1(B_356, k1_zfmisc_1(k2_zfmisc_1(A_355, A_355))) | ~v3_funct_2(B_356, A_355, A_355) | ~v1_funct_2(B_356, A_355, A_355) | ~v1_funct_1(B_356))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.32/2.48  tff(c_3715, plain, (![A_255]: (k2_funct_2(A_255, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_255, A_255) | ~v1_funct_2('#skF_1', A_255, A_255) | ~v1_funct_1('#skF_1') | A_255!='#skF_1')), inference(resolution, [status(thm)], [c_3443, c_3712])).
% 7.32/2.48  tff(c_3724, plain, (![A_357]: (k2_funct_2(A_357, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_357, A_357) | ~v1_funct_2('#skF_1', A_357, A_357) | A_357!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3715])).
% 7.32/2.48  tff(c_3727, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3270, c_3724])).
% 7.32/2.48  tff(c_3730, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3727])).
% 7.32/2.48  tff(c_3765, plain, (![A_363, B_364]: (v1_funct_2(k2_funct_2(A_363, B_364), A_363, A_363) | ~m1_subset_1(B_364, k1_zfmisc_1(k2_zfmisc_1(A_363, A_363))) | ~v3_funct_2(B_364, A_363, A_363) | ~v1_funct_2(B_364, A_363, A_363) | ~v1_funct_1(B_364))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.32/2.48  tff(c_3767, plain, (![A_255]: (v1_funct_2(k2_funct_2(A_255, '#skF_1'), A_255, A_255) | ~v3_funct_2('#skF_1', A_255, A_255) | ~v1_funct_2('#skF_1', A_255, A_255) | ~v1_funct_1('#skF_1') | A_255!='#skF_1')), inference(resolution, [status(thm)], [c_3443, c_3765])).
% 7.32/2.48  tff(c_3775, plain, (![A_365]: (v1_funct_2(k2_funct_2(A_365, '#skF_1'), A_365, A_365) | ~v3_funct_2('#skF_1', A_365, A_365) | ~v1_funct_2('#skF_1', A_365, A_365) | A_365!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3767])).
% 7.32/2.48  tff(c_3778, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3730, c_3775])).
% 7.32/2.48  tff(c_3781, plain, (v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3270, c_3778])).
% 7.32/2.48  tff(c_3444, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_2932])).
% 7.32/2.48  tff(c_3820, plain, (![A_373, B_374]: (m1_subset_1(k2_funct_2(A_373, B_374), k1_zfmisc_1(k2_zfmisc_1(A_373, A_373))) | ~m1_subset_1(B_374, k1_zfmisc_1(k2_zfmisc_1(A_373, A_373))) | ~v3_funct_2(B_374, A_373, A_373) | ~v1_funct_2(B_374, A_373, A_373) | ~v1_funct_1(B_374))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.32/2.48  tff(c_3871, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3730, c_3820])).
% 7.32/2.48  tff(c_3892, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3271, c_3270, c_3444, c_3871])).
% 7.32/2.48  tff(c_3266, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_2884])).
% 7.32/2.48  tff(c_3602, plain, (![B_23, C_24]: (k1_relset_1('#skF_1', B_23, C_24)='#skF_1' | ~v1_funct_2(C_24, '#skF_1', B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_23))))), inference(demodulation, [status(thm), theory('equality')], [c_3266, c_3266, c_3266, c_3266, c_46])).
% 7.32/2.48  tff(c_3917, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3892, c_3602])).
% 7.32/2.48  tff(c_3964, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3781, c_3917])).
% 7.32/2.48  tff(c_26, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.32/2.48  tff(c_3972, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_3892, c_26])).
% 7.32/2.48  tff(c_4032, plain, (k1_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3964, c_3972])).
% 7.32/2.48  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.32/2.48  tff(c_3937, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_3892, c_2])).
% 7.32/2.48  tff(c_3978, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_3937])).
% 7.32/2.48  tff(c_2886, plain, (![A_6]: (k1_relat_1(A_6)!='#skF_2' | A_6='#skF_2' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_2884, c_12])).
% 7.32/2.48  tff(c_3257, plain, (![A_6]: (k1_relat_1(A_6)!='#skF_1' | A_6='#skF_1' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_2886])).
% 7.32/2.48  tff(c_3985, plain, (k1_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_3978, c_3257])).
% 7.32/2.48  tff(c_4038, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4032, c_3985])).
% 7.32/2.48  tff(c_4079, plain, (k6_partfun1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4038, c_81])).
% 7.32/2.48  tff(c_4085, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3268, c_3272, c_3590, c_3308, c_3265, c_4079])).
% 7.32/2.48  tff(c_3694, plain, (![A_352, B_353]: (v1_funct_1(k2_funct_2(A_352, B_353)) | ~m1_subset_1(B_353, k1_zfmisc_1(k2_zfmisc_1(A_352, A_352))) | ~v3_funct_2(B_353, A_352, A_352) | ~v1_funct_2(B_353, A_352, A_352) | ~v1_funct_1(B_353))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.32/2.48  tff(c_3697, plain, (![A_255]: (v1_funct_1(k2_funct_2(A_255, '#skF_1')) | ~v3_funct_2('#skF_1', A_255, A_255) | ~v1_funct_2('#skF_1', A_255, A_255) | ~v1_funct_1('#skF_1') | A_255!='#skF_1')), inference(resolution, [status(thm)], [c_3443, c_3694])).
% 7.32/2.48  tff(c_3706, plain, (![A_354]: (v1_funct_1(k2_funct_2(A_354, '#skF_1')) | ~v3_funct_2('#skF_1', A_354, A_354) | ~v1_funct_2('#skF_1', A_354, A_354) | A_354!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3697])).
% 7.32/2.48  tff(c_3708, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3270, c_3706])).
% 7.32/2.48  tff(c_3711, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3708])).
% 7.32/2.48  tff(c_3731, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3730, c_3711])).
% 7.32/2.48  tff(c_3997, plain, (![C_375, E_379, F_377, A_378, D_380, B_376]: (k1_partfun1(A_378, B_376, C_375, D_380, E_379, F_377)=k5_relat_1(E_379, F_377) | ~m1_subset_1(F_377, k1_zfmisc_1(k2_zfmisc_1(C_375, D_380))) | ~v1_funct_1(F_377) | ~m1_subset_1(E_379, k1_zfmisc_1(k2_zfmisc_1(A_378, B_376))) | ~v1_funct_1(E_379))), inference(cnfTransformation, [status(thm)], [f_145])).
% 7.32/2.48  tff(c_3999, plain, (![A_378, B_376, E_379]: (k1_partfun1(A_378, B_376, '#skF_1', '#skF_1', E_379, k2_funct_1('#skF_1'))=k5_relat_1(E_379, k2_funct_1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~m1_subset_1(E_379, k1_zfmisc_1(k2_zfmisc_1(A_378, B_376))) | ~v1_funct_1(E_379))), inference(resolution, [status(thm)], [c_3892, c_3997])).
% 7.32/2.48  tff(c_4008, plain, (![A_378, B_376, E_379]: (k1_partfun1(A_378, B_376, '#skF_1', '#skF_1', E_379, k2_funct_1('#skF_1'))=k5_relat_1(E_379, k2_funct_1('#skF_1')) | ~m1_subset_1(E_379, k1_zfmisc_1(k2_zfmisc_1(A_378, B_376))) | ~v1_funct_1(E_379))), inference(demodulation, [status(thm), theory('equality')], [c_3731, c_3999])).
% 7.32/2.48  tff(c_4186, plain, (![A_390, B_391, E_392]: (k1_partfun1(A_390, B_391, '#skF_1', '#skF_1', E_392, '#skF_1')=k5_relat_1(E_392, '#skF_1') | ~m1_subset_1(E_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))) | ~v1_funct_1(E_392))), inference(demodulation, [status(thm), theory('equality')], [c_4038, c_4038, c_4008])).
% 7.32/2.48  tff(c_4192, plain, (![A_255]: (k1_partfun1(A_255, A_255, '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1') | A_255!='#skF_1')), inference(resolution, [status(thm)], [c_3443, c_4186])).
% 7.32/2.48  tff(c_4201, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_4085, c_4192])).
% 7.32/2.48  tff(c_3261, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_3255, c_174])).
% 7.32/2.48  tff(c_3425, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3308, c_3261])).
% 7.32/2.48  tff(c_3732, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3730, c_3425])).
% 7.32/2.48  tff(c_4054, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4038, c_3732])).
% 7.32/2.48  tff(c_4202, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4201, c_4054])).
% 7.32/2.48  tff(c_4205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3471, c_4202])).
% 7.32/2.48  tff(c_4206, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_72])).
% 7.32/2.48  tff(c_4879, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4875, c_4206])).
% 7.32/2.48  tff(c_5480, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5445, c_4879])).
% 7.32/2.48  tff(c_5487, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_82, c_5480])).
% 7.32/2.48  tff(c_5493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_80, c_4702, c_4570, c_4547, c_5487])).
% 7.32/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.32/2.48  
% 7.32/2.48  Inference rules
% 7.32/2.48  ----------------------
% 7.32/2.48  #Ref     : 0
% 7.32/2.48  #Sup     : 1108
% 7.32/2.48  #Fact    : 0
% 7.32/2.48  #Define  : 0
% 7.32/2.48  #Split   : 31
% 7.32/2.48  #Chain   : 0
% 7.32/2.48  #Close   : 0
% 7.32/2.48  
% 7.32/2.48  Ordering : KBO
% 7.32/2.48  
% 7.32/2.48  Simplification rules
% 7.32/2.48  ----------------------
% 7.32/2.48  #Subsume      : 149
% 7.32/2.48  #Demod        : 1806
% 7.32/2.48  #Tautology    : 508
% 7.32/2.48  #SimpNegUnit  : 45
% 7.32/2.48  #BackRed      : 127
% 7.32/2.48  
% 7.32/2.48  #Partial instantiations: 0
% 7.32/2.48  #Strategies tried      : 1
% 7.32/2.48  
% 7.32/2.48  Timing (in seconds)
% 7.32/2.48  ----------------------
% 7.32/2.48  Preprocessing        : 0.36
% 7.32/2.48  Parsing              : 0.19
% 7.32/2.48  CNF conversion       : 0.02
% 7.32/2.48  Main loop            : 1.30
% 7.32/2.48  Inferencing          : 0.44
% 7.32/2.48  Reduction            : 0.49
% 7.32/2.48  Demodulation         : 0.37
% 7.32/2.48  BG Simplification    : 0.04
% 7.32/2.48  Subsumption          : 0.22
% 7.32/2.48  Abstraction          : 0.05
% 7.32/2.48  MUC search           : 0.00
% 7.32/2.48  Cooper               : 0.00
% 7.32/2.48  Total                : 1.72
% 7.32/2.48  Index Insertion      : 0.00
% 7.32/2.48  Index Deletion       : 0.00
% 7.32/2.48  Index Matching       : 0.00
% 7.32/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
