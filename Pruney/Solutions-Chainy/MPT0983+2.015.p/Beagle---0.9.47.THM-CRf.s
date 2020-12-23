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
% DateTime   : Thu Dec  3 10:12:03 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 327 expanded)
%              Number of leaves         :   41 ( 136 expanded)
%              Depth                    :   11
%              Number of atoms          :  212 (1047 expanded)
%              Number of equality atoms :   31 ( 101 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_103,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_142,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_130,plain,(
    ! [A_53] :
      ( v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_99,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_133,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_99])).

tff(c_136,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_133])).

tff(c_137,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_44,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_1869,plain,(
    ! [A_383,E_386,F_384,B_382,D_381,C_385] :
      ( m1_subset_1(k1_partfun1(A_383,B_382,C_385,D_381,E_386,F_384),k1_zfmisc_1(k2_zfmisc_1(A_383,D_381)))
      | ~ m1_subset_1(F_384,k1_zfmisc_1(k2_zfmisc_1(C_385,D_381)))
      | ~ v1_funct_1(F_384)
      | ~ m1_subset_1(E_386,k1_zfmisc_1(k2_zfmisc_1(A_383,B_382)))
      | ~ v1_funct_1(E_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_34])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1759,plain,(
    ! [D_362,C_363,A_364,B_365] :
      ( D_362 = C_363
      | ~ r2_relset_1(A_364,B_365,C_363,D_362)
      | ~ m1_subset_1(D_362,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1769,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_1759])).

tff(c_1788,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1769])).

tff(c_1804,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1788])).

tff(c_1874,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1869,c_1804])).

tff(c_1902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_1874])).

tff(c_1903,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1788])).

tff(c_2150,plain,(
    ! [B_442,C_443,D_444,A_441,E_445] :
      ( k1_xboole_0 = C_443
      | v2_funct_1(D_444)
      | ~ v2_funct_1(k1_partfun1(A_441,B_442,B_442,C_443,D_444,E_445))
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(B_442,C_443)))
      | ~ v1_funct_2(E_445,B_442,C_443)
      | ~ v1_funct_1(E_445)
      | ~ m1_subset_1(D_444,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442)))
      | ~ v1_funct_2(D_444,A_441,B_442)
      | ~ v1_funct_1(D_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2152,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2150])).

tff(c_2157,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_56,c_68,c_2152])).

tff(c_2158,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2157])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2191,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2158,c_8])).

tff(c_2237,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2191,c_62])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_207,plain,(
    ! [C_70,B_71,A_72] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72)))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_222,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_207])).

tff(c_229,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_222])).

tff(c_2364,plain,(
    ! [C_458] :
      ( v1_xboole_0(C_458)
      | ~ m1_subset_1(C_458,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_229])).

tff(c_2370,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2237,c_2364])).

tff(c_2379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_2370])).

tff(c_2380,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2387,plain,(
    ! [C_459,A_460,B_461] :
      ( v1_relat_1(C_459)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2396,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2387])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2380,c_2396])).

tff(c_2407,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2440,plain,(
    ! [C_467,A_468,B_469] :
      ( v1_relat_1(C_467)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(A_468,B_469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2455,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2440])).

tff(c_2464,plain,(
    ! [C_472,B_473,A_474] :
      ( v5_relat_1(C_472,B_473)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_474,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2481,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_2464])).

tff(c_2534,plain,(
    ! [A_486,B_487,D_488] :
      ( r2_relset_1(A_486,B_487,D_488,D_488)
      | ~ m1_subset_1(D_488,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2545,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_67,c_2534])).

tff(c_2583,plain,(
    ! [A_493,B_494,C_495] :
      ( k2_relset_1(A_493,B_494,C_495) = k2_relat_1(C_495)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_493,B_494))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2600,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2583])).

tff(c_40,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2621,plain,(
    ! [D_500,C_501,A_502,B_503] :
      ( D_500 = C_501
      | ~ r2_relset_1(A_502,B_503,C_501,D_500)
      | ~ m1_subset_1(D_500,k1_zfmisc_1(k2_zfmisc_1(A_502,B_503)))
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(A_502,B_503))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2629,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_2621])).

tff(c_2644,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2629])).

tff(c_2664,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2644])).

tff(c_2835,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2664])).

tff(c_2839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_2835])).

tff(c_2840,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2644])).

tff(c_3169,plain,(
    ! [A_625,B_626,C_627,D_628] :
      ( k2_relset_1(A_625,B_626,C_627) = B_626
      | ~ r2_relset_1(B_626,B_626,k1_partfun1(B_626,A_625,A_625,B_626,D_628,C_627),k6_partfun1(B_626))
      | ~ m1_subset_1(D_628,k1_zfmisc_1(k2_zfmisc_1(B_626,A_625)))
      | ~ v1_funct_2(D_628,B_626,A_625)
      | ~ v1_funct_1(D_628)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_625,B_626)))
      | ~ v1_funct_2(C_627,A_625,B_626)
      | ~ v1_funct_1(C_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3172,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2840,c_3169])).

tff(c_3174,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_66,c_64,c_62,c_2545,c_2600,c_3172])).

tff(c_36,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3179,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3174,c_36])).

tff(c_3183,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2481,c_3174,c_3179])).

tff(c_3185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2407,c_3183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.14  
% 5.91/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.15  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.91/2.15  
% 5.91/2.15  %Foreground sorts:
% 5.91/2.15  
% 5.91/2.15  
% 5.91/2.15  %Background operators:
% 5.91/2.15  
% 5.91/2.15  
% 5.91/2.15  %Foreground operators:
% 5.91/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.91/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.91/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.91/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.91/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.91/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.91/2.15  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.91/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.91/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.91/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.91/2.15  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.91/2.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.91/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.91/2.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.91/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.91/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.91/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.91/2.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.91/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.91/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.91/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.91/2.15  
% 5.91/2.16  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 5.91/2.16  tff(f_48, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 5.91/2.16  tff(f_103, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.91/2.16  tff(f_50, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 5.91/2.16  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.91/2.16  tff(f_81, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.91/2.16  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.91/2.16  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 5.91/2.16  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.91/2.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.91/2.16  tff(f_67, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.91/2.16  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.91/2.16  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.91/2.16  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.91/2.16  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 5.91/2.16  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.91/2.16  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_130, plain, (![A_53]: (v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.91/2.16  tff(c_52, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_99, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 5.91/2.16  tff(c_133, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_130, c_99])).
% 5.91/2.16  tff(c_136, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_133])).
% 5.91/2.16  tff(c_137, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_136])).
% 5.91/2.16  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_44, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.91/2.16  tff(c_18, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.91/2.16  tff(c_68, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 5.91/2.16  tff(c_1869, plain, (![A_383, E_386, F_384, B_382, D_381, C_385]: (m1_subset_1(k1_partfun1(A_383, B_382, C_385, D_381, E_386, F_384), k1_zfmisc_1(k2_zfmisc_1(A_383, D_381))) | ~m1_subset_1(F_384, k1_zfmisc_1(k2_zfmisc_1(C_385, D_381))) | ~v1_funct_1(F_384) | ~m1_subset_1(E_386, k1_zfmisc_1(k2_zfmisc_1(A_383, B_382))) | ~v1_funct_1(E_386))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.91/2.16  tff(c_34, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.91/2.16  tff(c_67, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_34])).
% 5.91/2.16  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.91/2.16  tff(c_1759, plain, (![D_362, C_363, A_364, B_365]: (D_362=C_363 | ~r2_relset_1(A_364, B_365, C_363, D_362) | ~m1_subset_1(D_362, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.91/2.16  tff(c_1769, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_1759])).
% 5.91/2.16  tff(c_1788, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1769])).
% 5.91/2.16  tff(c_1804, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1788])).
% 5.91/2.16  tff(c_1874, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1869, c_1804])).
% 5.91/2.16  tff(c_1902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_1874])).
% 5.91/2.16  tff(c_1903, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1788])).
% 5.91/2.16  tff(c_2150, plain, (![B_442, C_443, D_444, A_441, E_445]: (k1_xboole_0=C_443 | v2_funct_1(D_444) | ~v2_funct_1(k1_partfun1(A_441, B_442, B_442, C_443, D_444, E_445)) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(B_442, C_443))) | ~v1_funct_2(E_445, B_442, C_443) | ~v1_funct_1(E_445) | ~m1_subset_1(D_444, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))) | ~v1_funct_2(D_444, A_441, B_442) | ~v1_funct_1(D_444))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.91/2.16  tff(c_2152, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2150])).
% 5.91/2.16  tff(c_2157, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_56, c_68, c_2152])).
% 5.91/2.16  tff(c_2158, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_99, c_2157])).
% 5.91/2.16  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.16  tff(c_2191, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2158, c_8])).
% 5.91/2.16  tff(c_2237, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2191, c_62])).
% 5.91/2.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.91/2.16  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.91/2.16  tff(c_207, plain, (![C_70, B_71, A_72]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.91/2.16  tff(c_222, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_207])).
% 5.91/2.16  tff(c_229, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_222])).
% 5.91/2.16  tff(c_2364, plain, (![C_458]: (v1_xboole_0(C_458) | ~m1_subset_1(C_458, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_229])).
% 5.91/2.16  tff(c_2370, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2237, c_2364])).
% 5.91/2.16  tff(c_2379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_2370])).
% 5.91/2.16  tff(c_2380, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_136])).
% 5.91/2.16  tff(c_2387, plain, (![C_459, A_460, B_461]: (v1_relat_1(C_459) | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.91/2.16  tff(c_2396, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2387])).
% 5.91/2.16  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2380, c_2396])).
% 5.91/2.16  tff(c_2407, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 5.91/2.16  tff(c_2440, plain, (![C_467, A_468, B_469]: (v1_relat_1(C_467) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(A_468, B_469))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.91/2.16  tff(c_2455, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2440])).
% 5.91/2.16  tff(c_2464, plain, (![C_472, B_473, A_474]: (v5_relat_1(C_472, B_473) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_474, B_473))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.91/2.16  tff(c_2481, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_2464])).
% 5.91/2.16  tff(c_2534, plain, (![A_486, B_487, D_488]: (r2_relset_1(A_486, B_487, D_488, D_488) | ~m1_subset_1(D_488, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.91/2.16  tff(c_2545, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_67, c_2534])).
% 5.91/2.16  tff(c_2583, plain, (![A_493, B_494, C_495]: (k2_relset_1(A_493, B_494, C_495)=k2_relat_1(C_495) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_493, B_494))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.91/2.16  tff(c_2600, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2583])).
% 5.91/2.16  tff(c_40, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.91/2.16  tff(c_2621, plain, (![D_500, C_501, A_502, B_503]: (D_500=C_501 | ~r2_relset_1(A_502, B_503, C_501, D_500) | ~m1_subset_1(D_500, k1_zfmisc_1(k2_zfmisc_1(A_502, B_503))) | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(A_502, B_503))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.91/2.16  tff(c_2629, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_54, c_2621])).
% 5.91/2.16  tff(c_2644, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2629])).
% 5.91/2.16  tff(c_2664, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2644])).
% 5.91/2.16  tff(c_2835, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2664])).
% 5.91/2.16  tff(c_2839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_2835])).
% 5.91/2.16  tff(c_2840, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2644])).
% 5.91/2.16  tff(c_3169, plain, (![A_625, B_626, C_627, D_628]: (k2_relset_1(A_625, B_626, C_627)=B_626 | ~r2_relset_1(B_626, B_626, k1_partfun1(B_626, A_625, A_625, B_626, D_628, C_627), k6_partfun1(B_626)) | ~m1_subset_1(D_628, k1_zfmisc_1(k2_zfmisc_1(B_626, A_625))) | ~v1_funct_2(D_628, B_626, A_625) | ~v1_funct_1(D_628) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_625, B_626))) | ~v1_funct_2(C_627, A_625, B_626) | ~v1_funct_1(C_627))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.91/2.16  tff(c_3172, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2840, c_3169])).
% 5.91/2.16  tff(c_3174, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_66, c_64, c_62, c_2545, c_2600, c_3172])).
% 5.91/2.16  tff(c_36, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.91/2.16  tff(c_3179, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3174, c_36])).
% 5.91/2.16  tff(c_3183, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2481, c_3174, c_3179])).
% 5.91/2.16  tff(c_3185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2407, c_3183])).
% 5.91/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.16  
% 5.91/2.16  Inference rules
% 5.91/2.16  ----------------------
% 5.91/2.16  #Ref     : 0
% 5.91/2.16  #Sup     : 702
% 5.91/2.16  #Fact    : 0
% 5.91/2.16  #Define  : 0
% 5.91/2.16  #Split   : 14
% 5.91/2.16  #Chain   : 0
% 5.91/2.16  #Close   : 0
% 5.91/2.16  
% 5.91/2.16  Ordering : KBO
% 5.91/2.16  
% 5.91/2.16  Simplification rules
% 5.91/2.16  ----------------------
% 5.91/2.17  #Subsume      : 16
% 5.91/2.17  #Demod        : 548
% 5.91/2.17  #Tautology    : 221
% 5.91/2.17  #SimpNegUnit  : 9
% 5.91/2.17  #BackRed      : 122
% 5.91/2.17  
% 5.91/2.17  #Partial instantiations: 0
% 5.91/2.17  #Strategies tried      : 1
% 5.91/2.17  
% 5.91/2.17  Timing (in seconds)
% 5.91/2.17  ----------------------
% 5.91/2.17  Preprocessing        : 0.37
% 5.91/2.17  Parsing              : 0.20
% 5.91/2.17  CNF conversion       : 0.03
% 5.91/2.17  Main loop            : 1.03
% 5.91/2.17  Inferencing          : 0.37
% 5.91/2.17  Reduction            : 0.36
% 5.91/2.17  Demodulation         : 0.26
% 5.91/2.17  BG Simplification    : 0.04
% 5.91/2.17  Subsumption          : 0.17
% 5.91/2.17  Abstraction          : 0.04
% 5.91/2.17  MUC search           : 0.00
% 5.91/2.17  Cooper               : 0.00
% 5.91/2.17  Total                : 1.44
% 5.91/2.17  Index Insertion      : 0.00
% 5.91/2.17  Index Deletion       : 0.00
% 5.91/2.17  Index Matching       : 0.00
% 5.91/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
