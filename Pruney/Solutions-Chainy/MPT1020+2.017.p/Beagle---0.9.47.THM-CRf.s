%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 12.18s
% Verified   : 
% Statistics : Number of formulae       :  329 (4996 expanded)
%              Number of leaves         :   50 (1572 expanded)
%              Depth                    :   18
%              Number of atoms          :  660 (14108 expanded)
%              Number of equality atoms :  176 (2882 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_175,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_150,axiom,(
    ! [A,B,C] :
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

tff(f_131,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_54,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_462,plain,(
    ! [A_105,B_106,D_107] :
      ( r2_relset_1(A_105,B_106,D_107,D_107)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_479,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_462])).

tff(c_80,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_426,plain,(
    ! [C_101,B_102,A_103] :
      ( v1_xboole_0(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(B_102,A_103)))
      | ~ v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_448,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_426])).

tff(c_461,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_86,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_84,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_173,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_193,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_173])).

tff(c_365,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_387,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_365])).

tff(c_493,plain,(
    ! [B_109,A_110] :
      ( k2_relat_1(B_109) = A_110
      | ~ v2_funct_2(B_109,A_110)
      | ~ v5_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_508,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_387,c_493])).

tff(c_521,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_508])).

tff(c_885,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_82,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1029,plain,(
    ! [C_147,B_148,A_149] :
      ( v2_funct_2(C_147,B_148)
      | ~ v3_funct_2(C_147,A_149,B_148)
      | ~ v1_funct_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1039,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1029])).

tff(c_1053,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1039])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_885,c_1053])).

tff(c_1056,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_1068,plain,(
    ! [A_150,B_151,C_152] :
      ( k2_relset_1(A_150,B_151,C_152) = k2_relat_1(C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1078,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1068])).

tff(c_1091,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1056,c_1078])).

tff(c_56,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_476,plain,(
    ! [A_39] : r2_relset_1(A_39,A_39,k6_partfun1(A_39),k6_partfun1(A_39)) ),
    inference(resolution,[status(thm)],[c_56,c_462])).

tff(c_1169,plain,(
    ! [C_156,A_157,B_158] :
      ( v2_funct_1(C_156)
      | ~ v3_funct_2(C_156,A_157,B_158)
      | ~ v1_funct_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1179,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1169])).

tff(c_1193,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_1179])).

tff(c_2006,plain,(
    ! [C_222,B_225,E_221,A_220,F_223,D_224] :
      ( m1_subset_1(k1_partfun1(A_220,B_225,C_222,D_224,E_221,F_223),k1_zfmisc_1(k2_zfmisc_1(A_220,D_224)))
      | ~ m1_subset_1(F_223,k1_zfmisc_1(k2_zfmisc_1(C_222,D_224)))
      | ~ v1_funct_1(F_223)
      | ~ m1_subset_1(E_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_225)))
      | ~ v1_funct_1(E_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1286,plain,(
    ! [D_170,C_171,A_172,B_173] :
      ( D_170 = C_171
      | ~ r2_relset_1(A_172,B_173,C_171,D_170)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1296,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_1286])).

tff(c_1315,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1296])).

tff(c_1364,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_2014,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2006,c_1364])).

tff(c_2059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_80,c_78,c_72,c_2014])).

tff(c_2060,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_4096,plain,(
    ! [C_325,D_326,B_327,A_328] :
      ( k2_funct_1(C_325) = D_326
      | k1_xboole_0 = B_327
      | k1_xboole_0 = A_328
      | ~ v2_funct_1(C_325)
      | ~ r2_relset_1(A_328,A_328,k1_partfun1(A_328,B_327,B_327,A_328,C_325,D_326),k6_partfun1(A_328))
      | k2_relset_1(A_328,B_327,C_325) != B_327
      | ~ m1_subset_1(D_326,k1_zfmisc_1(k2_zfmisc_1(B_327,A_328)))
      | ~ v1_funct_2(D_326,B_327,A_328)
      | ~ v1_funct_1(D_326)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_328,B_327)))
      | ~ v1_funct_2(C_325,A_328,B_327)
      | ~ v1_funct_1(C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4111,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_4096])).

tff(c_4119,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_76,c_72,c_1091,c_476,c_1193,c_4111])).

tff(c_4122,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4119])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4174,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4122,c_2])).

tff(c_4176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_4174])).

tff(c_4177,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4119])).

tff(c_2162,plain,(
    ! [A_238,B_239] :
      ( k2_funct_2(A_238,B_239) = k2_funct_1(B_239)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(k2_zfmisc_1(A_238,A_238)))
      | ~ v3_funct_2(B_239,A_238,A_238)
      | ~ v1_funct_2(B_239,A_238,A_238)
      | ~ v1_funct_1(B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2172,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_2162])).

tff(c_2189,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_2172])).

tff(c_68,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2193,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2189,c_68])).

tff(c_4190,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4177,c_2193])).

tff(c_4194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_4190])).

tff(c_4196,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_132,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_135,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_132])).

tff(c_4209,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4196,c_135])).

tff(c_4195,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_4202,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4195,c_135])).

tff(c_4237,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4209,c_4202])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4229,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4202,c_10])).

tff(c_4289,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4237,c_4229])).

tff(c_18,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4228,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4202,c_4202,c_18])).

tff(c_4360,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_1',B_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4237,c_4237,c_4228])).

tff(c_143,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_155,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_143])).

tff(c_247,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_264,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_247])).

tff(c_393,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_4361,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4360,c_393])).

tff(c_4366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_4361])).

tff(c_4367,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_4374,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_72])).

tff(c_9372,plain,(
    ! [A_641,B_642,D_643] :
      ( r2_relset_1(A_641,B_642,D_643,D_643)
      | ~ m1_subset_1(D_643,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9683,plain,(
    ! [D_683] :
      ( r2_relset_1('#skF_1','#skF_1',D_683,D_683)
      | ~ m1_subset_1(D_683,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_9372])).

tff(c_9695,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_4374,c_9683])).

tff(c_4419,plain,(
    ! [C_340,B_341,A_342] :
      ( v1_xboole_0(C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(B_341,A_342)))
      | ~ v1_xboole_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4422,plain,(
    ! [C_340] :
      ( v1_xboole_0(C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_4419])).

tff(c_9590,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4422])).

tff(c_4373,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_80])).

tff(c_4581,plain,(
    ! [B_350,A_351] :
      ( k2_relat_1(B_350) = A_351
      | ~ v2_funct_2(B_350,A_351)
      | ~ v5_relat_1(B_350,A_351)
      | ~ v1_relat_1(B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4593,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_387,c_4581])).

tff(c_4605,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_4593])).

tff(c_6929,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4605])).

tff(c_7216,plain,(
    ! [C_533,B_534,A_535] :
      ( v2_funct_2(C_533,B_534)
      | ~ v3_funct_2(C_533,A_535,B_534)
      | ~ v1_funct_1(C_533)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_535,B_534))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9317,plain,(
    ! [C_638] :
      ( v2_funct_2(C_638,'#skF_1')
      | ~ v3_funct_2(C_638,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_638)
      | ~ m1_subset_1(C_638,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_7216])).

tff(c_9326,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4373,c_9317])).

tff(c_9337,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_9326])).

tff(c_9339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6929,c_9337])).

tff(c_9340,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4605])).

tff(c_9456,plain,(
    ! [A_653,B_654,C_655] :
      ( k2_relset_1(A_653,B_654,C_655) = k2_relat_1(C_655)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_653,B_654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11097,plain,(
    ! [C_755] :
      ( k2_relset_1('#skF_1','#skF_1',C_755) = k2_relat_1(C_755)
      | ~ m1_subset_1(C_755,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_9456])).

tff(c_11106,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4373,c_11097])).

tff(c_11116,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9340,c_11106])).

tff(c_11454,plain,(
    ! [C_760,A_761,B_762,D_763] :
      ( v2_funct_1(C_760)
      | ~ r2_relset_1(A_761,A_761,k1_partfun1(A_761,B_762,B_762,A_761,C_760,D_763),k6_partfun1(A_761))
      | ~ m1_subset_1(D_763,k1_zfmisc_1(k2_zfmisc_1(B_762,A_761)))
      | ~ v1_funct_2(D_763,B_762,A_761)
      | ~ v1_funct_1(D_763)
      | ~ m1_subset_1(C_760,k1_zfmisc_1(k2_zfmisc_1(A_761,B_762)))
      | ~ v1_funct_2(C_760,A_761,B_762)
      | ~ v1_funct_1(C_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_11475,plain,
    ( v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_11454])).

tff(c_11479,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4373,c_4367,c_78,c_76,c_4374,c_4367,c_11475])).

tff(c_12009,plain,(
    ! [C_794,D_795,B_796,A_797] :
      ( k2_funct_1(C_794) = D_795
      | k1_xboole_0 = B_796
      | k1_xboole_0 = A_797
      | ~ v2_funct_1(C_794)
      | ~ r2_relset_1(A_797,A_797,k1_partfun1(A_797,B_796,B_796,A_797,C_794,D_795),k6_partfun1(A_797))
      | k2_relset_1(A_797,B_796,C_794) != B_796
      | ~ m1_subset_1(D_795,k1_zfmisc_1(k2_zfmisc_1(B_796,A_797)))
      | ~ v1_funct_2(D_795,B_796,A_797)
      | ~ v1_funct_1(D_795)
      | ~ m1_subset_1(C_794,k1_zfmisc_1(k2_zfmisc_1(A_797,B_796)))
      | ~ v1_funct_2(C_794,A_797,B_796)
      | ~ v1_funct_1(C_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_12030,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_12009])).

tff(c_12035,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4373,c_4367,c_78,c_76,c_4374,c_4367,c_11116,c_11479,c_12030])).

tff(c_12036,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12035])).

tff(c_12093,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12036,c_2])).

tff(c_12095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9590,c_12093])).

tff(c_12096,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12035])).

tff(c_9869,plain,(
    ! [A_707,B_708] :
      ( k2_funct_2(A_707,B_708) = k2_funct_1(B_708)
      | ~ m1_subset_1(B_708,k1_zfmisc_1(k2_zfmisc_1(A_707,A_707)))
      | ~ v3_funct_2(B_708,A_707,A_707)
      | ~ v1_funct_2(B_708,A_707,A_707)
      | ~ v1_funct_1(B_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12383,plain,(
    ! [B_811] :
      ( k2_funct_2('#skF_1',B_811) = k2_funct_1(B_811)
      | ~ m1_subset_1(B_811,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_811,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_811,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_811) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_9869])).

tff(c_12392,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4373,c_12383])).

tff(c_12404,plain,(
    k2_funct_2('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_12096,c_12392])).

tff(c_12406,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12404,c_68])).

tff(c_12409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9695,c_12406])).

tff(c_12411,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4422])).

tff(c_12421,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12411,c_135])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4388,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4367,c_14])).

tff(c_4580,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4388])).

tff(c_12434,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12421,c_4580])).

tff(c_12450,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_1',B_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12421,c_12421,c_18])).

tff(c_12600,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12450,c_4367])).

tff(c_12602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12434,c_12600])).

tff(c_12604,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4388])).

tff(c_12650,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12604,c_10])).

tff(c_154,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_143])).

tff(c_265,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_247])).

tff(c_339,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_4370,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_339])).

tff(c_12695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12650,c_4370])).

tff(c_12696,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_12701,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12696,c_72])).

tff(c_16127,plain,(
    ! [A_1074,B_1075,D_1076] :
      ( r2_relset_1(A_1074,B_1075,D_1076,D_1076)
      | ~ m1_subset_1(D_1076,k1_zfmisc_1(k2_zfmisc_1(A_1074,B_1075))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16218,plain,(
    ! [D_1089] :
      ( r2_relset_1('#skF_1','#skF_1',D_1089,D_1089)
      | ~ m1_subset_1(D_1089,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_16127])).

tff(c_16230,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_12701,c_16218])).

tff(c_12871,plain,(
    ! [C_838,B_839,A_840] :
      ( v1_xboole_0(C_838)
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(B_839,A_840)))
      | ~ v1_xboole_0(A_840) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12874,plain,(
    ! [C_838] :
      ( v1_xboole_0(C_838)
      | ~ m1_subset_1(C_838,k1_zfmisc_1('#skF_2'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_12871])).

tff(c_16166,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12874])).

tff(c_12700,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12696,c_80])).

tff(c_12724,plain,(
    ! [C_824,B_825,A_826] :
      ( v5_relat_1(C_824,B_825)
      | ~ m1_subset_1(C_824,k1_zfmisc_1(k2_zfmisc_1(A_826,B_825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_13065,plain,(
    ! [C_854] :
      ( v5_relat_1(C_854,'#skF_1')
      | ~ m1_subset_1(C_854,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_12724])).

tff(c_13082,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12700,c_13065])).

tff(c_48,plain,(
    ! [B_32,A_31] :
      ( k2_relat_1(B_32) = A_31
      | ~ v2_funct_2(B_32,A_31)
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_13092,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13082,c_48])).

tff(c_13095,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_13092])).

tff(c_14589,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_13095])).

tff(c_14828,plain,(
    ! [C_993,B_994,A_995] :
      ( v2_funct_2(C_993,B_994)
      | ~ v3_funct_2(C_993,A_995,B_994)
      | ~ v1_funct_1(C_993)
      | ~ m1_subset_1(C_993,k1_zfmisc_1(k2_zfmisc_1(A_995,B_994))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16081,plain,(
    ! [C_1070] :
      ( v2_funct_2(C_1070,'#skF_1')
      | ~ v3_funct_2(C_1070,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1070)
      | ~ m1_subset_1(C_1070,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_14828])).

tff(c_16090,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12700,c_16081])).

tff(c_16101,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_16090])).

tff(c_16103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14589,c_16101])).

tff(c_16104,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_13095])).

tff(c_16183,plain,(
    ! [A_1085,B_1086,C_1087] :
      ( k2_relset_1(A_1085,B_1086,C_1087) = k2_relat_1(C_1087)
      | ~ m1_subset_1(C_1087,k1_zfmisc_1(k2_zfmisc_1(A_1085,B_1086))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16315,plain,(
    ! [C_1101] :
      ( k2_relset_1('#skF_1','#skF_1',C_1101) = k2_relat_1(C_1101)
      | ~ m1_subset_1(C_1101,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_16183])).

tff(c_16324,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12700,c_16315])).

tff(c_16334,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16104,c_16324])).

tff(c_16241,plain,(
    ! [C_1092,A_1093,B_1094] :
      ( v2_funct_1(C_1092)
      | ~ v3_funct_2(C_1092,A_1093,B_1094)
      | ~ v1_funct_1(C_1092)
      | ~ m1_subset_1(C_1092,k1_zfmisc_1(k2_zfmisc_1(A_1093,B_1094))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16428,plain,(
    ! [C_1113] :
      ( v2_funct_1(C_1113)
      | ~ v3_funct_2(C_1113,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1113)
      | ~ m1_subset_1(C_1113,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_16241])).

tff(c_16437,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12700,c_16428])).

tff(c_16448,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_16437])).

tff(c_18924,plain,(
    ! [C_1227,D_1228,B_1229,A_1230] :
      ( k2_funct_1(C_1227) = D_1228
      | k1_xboole_0 = B_1229
      | k1_xboole_0 = A_1230
      | ~ v2_funct_1(C_1227)
      | ~ r2_relset_1(A_1230,A_1230,k1_partfun1(A_1230,B_1229,B_1229,A_1230,C_1227,D_1228),k6_partfun1(A_1230))
      | k2_relset_1(A_1230,B_1229,C_1227) != B_1229
      | ~ m1_subset_1(D_1228,k1_zfmisc_1(k2_zfmisc_1(B_1229,A_1230)))
      | ~ v1_funct_2(D_1228,B_1229,A_1230)
      | ~ v1_funct_1(D_1228)
      | ~ m1_subset_1(C_1227,k1_zfmisc_1(k2_zfmisc_1(A_1230,B_1229)))
      | ~ v1_funct_2(C_1227,A_1230,B_1229)
      | ~ v1_funct_1(C_1227) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_18945,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_18924])).

tff(c_18950,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_12700,c_12696,c_78,c_76,c_12701,c_12696,c_16334,c_16448,c_18945])).

tff(c_18951,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18950])).

tff(c_19009,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18951,c_2])).

tff(c_19011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16166,c_19009])).

tff(c_19012,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18950])).

tff(c_16955,plain,(
    ! [A_1136,B_1137] :
      ( k2_funct_2(A_1136,B_1137) = k2_funct_1(B_1137)
      | ~ m1_subset_1(B_1137,k1_zfmisc_1(k2_zfmisc_1(A_1136,A_1136)))
      | ~ v3_funct_2(B_1137,A_1136,A_1136)
      | ~ v1_funct_2(B_1137,A_1136,A_1136)
      | ~ v1_funct_1(B_1137) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_18333,plain,(
    ! [B_1199] :
      ( k2_funct_2('#skF_1',B_1199) = k2_funct_1(B_1199)
      | ~ m1_subset_1(B_1199,k1_zfmisc_1('#skF_2'))
      | ~ v3_funct_2(B_1199,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1199,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_16955])).

tff(c_18342,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12700,c_18333])).

tff(c_18354,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_18342])).

tff(c_18360,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18354,c_68])).

tff(c_19014,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19012,c_18360])).

tff(c_19018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16230,c_19014])).

tff(c_19020,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_12874])).

tff(c_19030,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_19020,c_135])).

tff(c_12712,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_14])).

tff(c_12826,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12712])).

tff(c_19044,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19030,c_12826])).

tff(c_16,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19055,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19030,c_19030,c_16])).

tff(c_19190,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19055,c_12696])).

tff(c_19192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19044,c_19190])).

tff(c_19194,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12712])).

tff(c_19209,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19194,c_10])).

tff(c_12698,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12696,c_155])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12723,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12698,c_4])).

tff(c_12774,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12723])).

tff(c_19235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19209,c_12774])).

tff(c_19236,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12723])).

tff(c_19239,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19236,c_12701])).

tff(c_19242,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19236,c_12696])).

tff(c_19486,plain,(
    ! [A_1258,B_1259,D_1260] :
      ( r2_relset_1(A_1258,B_1259,D_1260,D_1260)
      | ~ m1_subset_1(D_1260,k1_zfmisc_1(k2_zfmisc_1(A_1258,B_1259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22114,plain,(
    ! [D_1441] :
      ( r2_relset_1('#skF_1','#skF_1',D_1441,D_1441)
      | ~ m1_subset_1(D_1441,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19242,c_19486])).

tff(c_22124,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_19239,c_22114])).

tff(c_74,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_19337,plain,(
    ! [C_1247,B_1248,A_1249] :
      ( v1_xboole_0(C_1247)
      | ~ m1_subset_1(C_1247,k1_zfmisc_1(k2_zfmisc_1(B_1248,A_1249)))
      | ~ v1_xboole_0(A_1249) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_19340,plain,(
    ! [C_1247] :
      ( v1_xboole_0(C_1247)
      | ~ m1_subset_1(C_1247,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19242,c_19337])).

tff(c_22028,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_19340])).

tff(c_194,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_173])).

tff(c_12727,plain,(
    ! [C_824] :
      ( v5_relat_1(C_824,'#skF_1')
      | ~ m1_subset_1(C_824,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_12724])).

tff(c_19600,plain,(
    ! [C_1276] :
      ( v5_relat_1(C_1276,'#skF_1')
      | ~ m1_subset_1(C_1276,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19236,c_12727])).

tff(c_19613,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_19239,c_19600])).

tff(c_19617,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19613,c_48])).

tff(c_19620,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_19617])).

tff(c_19626,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_19620])).

tff(c_19244,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19236,c_70])).

tff(c_21837,plain,(
    ! [D_1401,A_1402,B_1403,C_1404] :
      ( v2_funct_2(D_1401,A_1402)
      | ~ r2_relset_1(A_1402,A_1402,k1_partfun1(A_1402,B_1403,B_1403,A_1402,C_1404,D_1401),k6_partfun1(A_1402))
      | ~ m1_subset_1(D_1401,k1_zfmisc_1(k2_zfmisc_1(B_1403,A_1402)))
      | ~ v1_funct_2(D_1401,B_1403,A_1402)
      | ~ v1_funct_1(D_1401)
      | ~ m1_subset_1(C_1404,k1_zfmisc_1(k2_zfmisc_1(A_1402,B_1403)))
      | ~ v1_funct_2(C_1404,A_1402,B_1403)
      | ~ v1_funct_1(C_1404) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_21855,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19244,c_21837])).

tff(c_21861,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_19239,c_19242,c_21855])).

tff(c_21863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19626,c_21861])).

tff(c_21864,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19620])).

tff(c_21916,plain,(
    ! [A_1411,B_1412,C_1413] :
      ( k2_relset_1(A_1411,B_1412,C_1413) = k2_relat_1(C_1413)
      | ~ m1_subset_1(C_1413,k1_zfmisc_1(k2_zfmisc_1(A_1411,B_1412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_23887,plain,(
    ! [C_1514] :
      ( k2_relset_1('#skF_1','#skF_1',C_1514) = k2_relat_1(C_1514)
      | ~ m1_subset_1(C_1514,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19242,c_21916])).

tff(c_23893,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19239,c_23887])).

tff(c_23901,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21864,c_23893])).

tff(c_24023,plain,(
    ! [C_1522,A_1523,B_1524,D_1525] :
      ( v2_funct_1(C_1522)
      | ~ r2_relset_1(A_1523,A_1523,k1_partfun1(A_1523,B_1524,B_1524,A_1523,C_1522,D_1525),k6_partfun1(A_1523))
      | ~ m1_subset_1(D_1525,k1_zfmisc_1(k2_zfmisc_1(B_1524,A_1523)))
      | ~ v1_funct_2(D_1525,B_1524,A_1523)
      | ~ v1_funct_1(D_1525)
      | ~ m1_subset_1(C_1522,k1_zfmisc_1(k2_zfmisc_1(A_1523,B_1524)))
      | ~ v1_funct_2(C_1522,A_1523,B_1524)
      | ~ v1_funct_1(C_1522) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_24041,plain,
    ( v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19244,c_24023])).

tff(c_24047,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_19239,c_19242,c_24041])).

tff(c_25201,plain,(
    ! [C_1557,D_1558,B_1559,A_1560] :
      ( k2_funct_1(C_1557) = D_1558
      | k1_xboole_0 = B_1559
      | k1_xboole_0 = A_1560
      | ~ v2_funct_1(C_1557)
      | ~ r2_relset_1(A_1560,A_1560,k1_partfun1(A_1560,B_1559,B_1559,A_1560,C_1557,D_1558),k6_partfun1(A_1560))
      | k2_relset_1(A_1560,B_1559,C_1557) != B_1559
      | ~ m1_subset_1(D_1558,k1_zfmisc_1(k2_zfmisc_1(B_1559,A_1560)))
      | ~ v1_funct_2(D_1558,B_1559,A_1560)
      | ~ v1_funct_1(D_1558)
      | ~ m1_subset_1(C_1557,k1_zfmisc_1(k2_zfmisc_1(A_1560,B_1559)))
      | ~ v1_funct_2(C_1557,A_1560,B_1559)
      | ~ v1_funct_1(C_1557) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_25222,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19244,c_25201])).

tff(c_25228,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_19239,c_19242,c_23901,c_24047,c_25222])).

tff(c_25231,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_25228])).

tff(c_25292,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25231,c_2])).

tff(c_25294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22028,c_25292])).

tff(c_25295,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25228])).

tff(c_22643,plain,(
    ! [A_1467,B_1468] :
      ( k2_funct_2(A_1467,B_1468) = k2_funct_1(B_1468)
      | ~ m1_subset_1(B_1468,k1_zfmisc_1(k2_zfmisc_1(A_1467,A_1467)))
      | ~ v3_funct_2(B_1468,A_1467,A_1467)
      | ~ v1_funct_2(B_1468,A_1467,A_1467)
      | ~ v1_funct_1(B_1468) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_26116,plain,(
    ! [B_1574] :
      ( k2_funct_2('#skF_1',B_1574) = k2_funct_1(B_1574)
      | ~ m1_subset_1(B_1574,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_1574,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_1574,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_1574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19242,c_22643])).

tff(c_26122,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_19239,c_26116])).

tff(c_26131,plain,(
    k2_funct_2('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_25295,c_26122])).

tff(c_19246,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19236,c_68])).

tff(c_26133,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26131,c_19246])).

tff(c_26136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22124,c_26133])).

tff(c_26138,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_19340])).

tff(c_26151,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26138,c_135])).

tff(c_19335,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19236,c_12712])).

tff(c_19336,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19335])).

tff(c_26169,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26151,c_19336])).

tff(c_26181,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_1',B_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26151,c_26151,c_18])).

tff(c_26366,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26181,c_19242])).

tff(c_26368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26169,c_26366])).

tff(c_26370,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19335])).

tff(c_26369,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_19335])).

tff(c_26539,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26370,c_26370,c_26369])).

tff(c_26540,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26539])).

tff(c_26385,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26370,c_10])).

tff(c_26562,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26540,c_26385])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26625,plain,(
    ! [A_1598,B_1599,D_1600] :
      ( r2_relset_1(A_1598,B_1599,D_1600,D_1600)
      | ~ m1_subset_1(D_1600,k1_zfmisc_1(k2_zfmisc_1(A_1598,B_1599))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30202,plain,(
    ! [A_1847,B_1848,A_1849] :
      ( r2_relset_1(A_1847,B_1848,A_1849,A_1849)
      | ~ r1_tarski(A_1849,k2_zfmisc_1(A_1847,B_1848)) ) ),
    inference(resolution,[status(thm)],[c_22,c_26625])).

tff(c_30219,plain,(
    ! [A_1847,B_1848] : r2_relset_1(A_1847,B_1848,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_26562,c_30202])).

tff(c_26578,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26540,c_78])).

tff(c_156,plain,(
    ! [A_68] : m1_subset_1(k6_partfun1(A_68),k1_zfmisc_1(k2_zfmisc_1(A_68,A_68))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_163,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_172,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_163,c_20])).

tff(c_251,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_172,c_247])).

tff(c_263,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_251])).

tff(c_26377,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26370,c_26370,c_263])).

tff(c_26561,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26540,c_26540,c_26377])).

tff(c_26576,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26540,c_76])).

tff(c_26577,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26540,c_74])).

tff(c_60,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_24,plain,(
    ! [A_10] : k2_funct_1(k6_relat_1(A_10)) = k6_relat_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_10] : k2_funct_1(k6_partfun1(A_10)) = k6_partfun1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_24])).

tff(c_29228,plain,(
    ! [A_1763,B_1764] :
      ( k2_funct_2(A_1763,B_1764) = k2_funct_1(B_1764)
      | ~ m1_subset_1(B_1764,k1_zfmisc_1(k2_zfmisc_1(A_1763,A_1763)))
      | ~ v3_funct_2(B_1764,A_1763,A_1763)
      | ~ v1_funct_2(B_1764,A_1763,A_1763)
      | ~ v1_funct_1(B_1764) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_29239,plain,(
    ! [A_39] :
      ( k2_funct_2(A_39,k6_partfun1(A_39)) = k2_funct_1(k6_partfun1(A_39))
      | ~ v3_funct_2(k6_partfun1(A_39),A_39,A_39)
      | ~ v1_funct_2(k6_partfun1(A_39),A_39,A_39)
      | ~ v1_funct_1(k6_partfun1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_56,c_29228])).

tff(c_33772,plain,(
    ! [A_1955] :
      ( k2_funct_2(A_1955,k6_partfun1(A_1955)) = k6_partfun1(A_1955)
      | ~ v3_funct_2(k6_partfun1(A_1955),A_1955,A_1955)
      | ~ v1_funct_2(k6_partfun1(A_1955),A_1955,A_1955)
      | ~ v1_funct_1(k6_partfun1(A_1955)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_29239])).

tff(c_33796,plain,
    ( k2_funct_2('#skF_1',k6_partfun1('#skF_1')) = k6_partfun1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2(k6_partfun1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26561,c_33772])).

tff(c_33798,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26578,c_26561,c_26576,c_26561,c_26577,c_26561,c_26561,c_33796])).

tff(c_26572,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26540,c_26540,c_19246])).

tff(c_33799,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33798,c_26572])).

tff(c_33802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30219,c_33799])).

tff(c_33803,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26539])).

tff(c_33804,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26539])).

tff(c_33835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33803,c_33804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:12:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.80/4.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.80/4.81  
% 11.80/4.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.80/4.81  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.80/4.81  
% 11.80/4.81  %Foreground sorts:
% 11.80/4.81  
% 11.80/4.81  
% 11.80/4.81  %Background operators:
% 11.80/4.81  
% 11.80/4.81  
% 11.80/4.81  %Foreground operators:
% 11.80/4.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.80/4.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.80/4.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.80/4.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.80/4.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.80/4.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.80/4.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.80/4.81  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 11.80/4.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.80/4.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.80/4.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.80/4.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.80/4.81  tff('#skF_2', type, '#skF_2': $i).
% 11.80/4.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.80/4.81  tff('#skF_3', type, '#skF_3': $i).
% 11.80/4.81  tff('#skF_1', type, '#skF_1': $i).
% 11.80/4.81  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 11.80/4.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.80/4.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.80/4.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.80/4.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.80/4.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.80/4.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.80/4.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.80/4.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.80/4.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.80/4.81  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 11.80/4.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.80/4.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.80/4.81  
% 12.18/4.85  tff(f_197, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 12.18/4.85  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.18/4.85  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 12.18/4.85  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.18/4.85  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.18/4.85  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 12.18/4.85  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 12.18/4.85  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.18/4.85  tff(f_119, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 12.18/4.85  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.18/4.85  tff(f_175, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 12.18/4.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.18/4.85  tff(f_129, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 12.18/4.85  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 12.18/4.85  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.18/4.85  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.18/4.85  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 12.18/4.85  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.18/4.85  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 12.18/4.85  tff(f_131, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.18/4.85  tff(f_54, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 12.18/4.85  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_462, plain, (![A_105, B_106, D_107]: (r2_relset_1(A_105, B_106, D_107, D_107) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.18/4.85  tff(c_479, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_462])).
% 12.18/4.85  tff(c_80, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_426, plain, (![C_101, B_102, A_103]: (v1_xboole_0(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(B_102, A_103))) | ~v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.18/4.85  tff(c_448, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_426])).
% 12.18/4.85  tff(c_461, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_448])).
% 12.18/4.85  tff(c_86, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_84, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_173, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.18/4.85  tff(c_193, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_173])).
% 12.18/4.85  tff(c_365, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.18/4.85  tff(c_387, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_80, c_365])).
% 12.18/4.85  tff(c_493, plain, (![B_109, A_110]: (k2_relat_1(B_109)=A_110 | ~v2_funct_2(B_109, A_110) | ~v5_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.18/4.85  tff(c_508, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_387, c_493])).
% 12.18/4.85  tff(c_521, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_508])).
% 12.18/4.85  tff(c_885, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_521])).
% 12.18/4.85  tff(c_82, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_1029, plain, (![C_147, B_148, A_149]: (v2_funct_2(C_147, B_148) | ~v3_funct_2(C_147, A_149, B_148) | ~v1_funct_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.18/4.85  tff(c_1039, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1029])).
% 12.18/4.85  tff(c_1053, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1039])).
% 12.18/4.85  tff(c_1055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_885, c_1053])).
% 12.18/4.85  tff(c_1056, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_521])).
% 12.18/4.85  tff(c_1068, plain, (![A_150, B_151, C_152]: (k2_relset_1(A_150, B_151, C_152)=k2_relat_1(C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.18/4.85  tff(c_1078, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1068])).
% 12.18/4.85  tff(c_1091, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1056, c_1078])).
% 12.18/4.85  tff(c_56, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.18/4.85  tff(c_476, plain, (![A_39]: (r2_relset_1(A_39, A_39, k6_partfun1(A_39), k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_56, c_462])).
% 12.18/4.85  tff(c_1169, plain, (![C_156, A_157, B_158]: (v2_funct_1(C_156) | ~v3_funct_2(C_156, A_157, B_158) | ~v1_funct_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.18/4.85  tff(c_1179, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1169])).
% 12.18/4.85  tff(c_1193, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_1179])).
% 12.18/4.85  tff(c_2006, plain, (![C_222, B_225, E_221, A_220, F_223, D_224]: (m1_subset_1(k1_partfun1(A_220, B_225, C_222, D_224, E_221, F_223), k1_zfmisc_1(k2_zfmisc_1(A_220, D_224))) | ~m1_subset_1(F_223, k1_zfmisc_1(k2_zfmisc_1(C_222, D_224))) | ~v1_funct_1(F_223) | ~m1_subset_1(E_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_225))) | ~v1_funct_1(E_221))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.18/4.85  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_1286, plain, (![D_170, C_171, A_172, B_173]: (D_170=C_171 | ~r2_relset_1(A_172, B_173, C_171, D_170) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.18/4.85  tff(c_1296, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_1286])).
% 12.18/4.85  tff(c_1315, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1296])).
% 12.18/4.85  tff(c_1364, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1315])).
% 12.18/4.85  tff(c_2014, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_2006, c_1364])).
% 12.18/4.85  tff(c_2059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_80, c_78, c_72, c_2014])).
% 12.18/4.85  tff(c_2060, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1315])).
% 12.18/4.85  tff(c_4096, plain, (![C_325, D_326, B_327, A_328]: (k2_funct_1(C_325)=D_326 | k1_xboole_0=B_327 | k1_xboole_0=A_328 | ~v2_funct_1(C_325) | ~r2_relset_1(A_328, A_328, k1_partfun1(A_328, B_327, B_327, A_328, C_325, D_326), k6_partfun1(A_328)) | k2_relset_1(A_328, B_327, C_325)!=B_327 | ~m1_subset_1(D_326, k1_zfmisc_1(k2_zfmisc_1(B_327, A_328))) | ~v1_funct_2(D_326, B_327, A_328) | ~v1_funct_1(D_326) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_328, B_327))) | ~v1_funct_2(C_325, A_328, B_327) | ~v1_funct_1(C_325))), inference(cnfTransformation, [status(thm)], [f_175])).
% 12.18/4.85  tff(c_4111, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2060, c_4096])).
% 12.18/4.85  tff(c_4119, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_76, c_72, c_1091, c_476, c_1193, c_4111])).
% 12.18/4.85  tff(c_4122, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_4119])).
% 12.18/4.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.18/4.85  tff(c_4174, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4122, c_2])).
% 12.18/4.85  tff(c_4176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_4174])).
% 12.18/4.85  tff(c_4177, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_4119])).
% 12.18/4.85  tff(c_2162, plain, (![A_238, B_239]: (k2_funct_2(A_238, B_239)=k2_funct_1(B_239) | ~m1_subset_1(B_239, k1_zfmisc_1(k2_zfmisc_1(A_238, A_238))) | ~v3_funct_2(B_239, A_238, A_238) | ~v1_funct_2(B_239, A_238, A_238) | ~v1_funct_1(B_239))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.18/4.85  tff(c_2172, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_2162])).
% 12.18/4.85  tff(c_2189, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_2172])).
% 12.18/4.85  tff(c_68, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_2193, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2189, c_68])).
% 12.18/4.85  tff(c_4190, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4177, c_2193])).
% 12.18/4.85  tff(c_4194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_479, c_4190])).
% 12.18/4.85  tff(c_4196, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_448])).
% 12.18/4.85  tff(c_132, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.18/4.85  tff(c_135, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_2, c_132])).
% 12.18/4.85  tff(c_4209, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4196, c_135])).
% 12.18/4.85  tff(c_4195, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_448])).
% 12.18/4.85  tff(c_4202, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4195, c_135])).
% 12.18/4.85  tff(c_4237, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4209, c_4202])).
% 12.18/4.85  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.18/4.85  tff(c_4229, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4202, c_10])).
% 12.18/4.85  tff(c_4289, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4237, c_4229])).
% 12.18/4.85  tff(c_18, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.18/4.85  tff(c_4228, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4202, c_4202, c_18])).
% 12.18/4.85  tff(c_4360, plain, (![B_7]: (k2_zfmisc_1('#skF_1', B_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4237, c_4237, c_4228])).
% 12.18/4.85  tff(c_143, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.18/4.85  tff(c_155, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_143])).
% 12.18/4.85  tff(c_247, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.18/4.85  tff(c_264, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_155, c_247])).
% 12.18/4.85  tff(c_393, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 12.18/4.85  tff(c_4361, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4360, c_393])).
% 12.18/4.85  tff(c_4366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4289, c_4361])).
% 12.18/4.85  tff(c_4367, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_264])).
% 12.18/4.85  tff(c_4374, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_72])).
% 12.18/4.85  tff(c_9372, plain, (![A_641, B_642, D_643]: (r2_relset_1(A_641, B_642, D_643, D_643) | ~m1_subset_1(D_643, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.18/4.85  tff(c_9683, plain, (![D_683]: (r2_relset_1('#skF_1', '#skF_1', D_683, D_683) | ~m1_subset_1(D_683, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_9372])).
% 12.18/4.85  tff(c_9695, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_4374, c_9683])).
% 12.18/4.85  tff(c_4419, plain, (![C_340, B_341, A_342]: (v1_xboole_0(C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(B_341, A_342))) | ~v1_xboole_0(A_342))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.18/4.85  tff(c_4422, plain, (![C_340]: (v1_xboole_0(C_340) | ~m1_subset_1(C_340, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_4419])).
% 12.18/4.85  tff(c_9590, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4422])).
% 12.18/4.85  tff(c_4373, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_80])).
% 12.18/4.85  tff(c_4581, plain, (![B_350, A_351]: (k2_relat_1(B_350)=A_351 | ~v2_funct_2(B_350, A_351) | ~v5_relat_1(B_350, A_351) | ~v1_relat_1(B_350))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.18/4.85  tff(c_4593, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_387, c_4581])).
% 12.18/4.85  tff(c_4605, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_4593])).
% 12.18/4.85  tff(c_6929, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4605])).
% 12.18/4.85  tff(c_7216, plain, (![C_533, B_534, A_535]: (v2_funct_2(C_533, B_534) | ~v3_funct_2(C_533, A_535, B_534) | ~v1_funct_1(C_533) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_535, B_534))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.18/4.85  tff(c_9317, plain, (![C_638]: (v2_funct_2(C_638, '#skF_1') | ~v3_funct_2(C_638, '#skF_1', '#skF_1') | ~v1_funct_1(C_638) | ~m1_subset_1(C_638, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_7216])).
% 12.18/4.85  tff(c_9326, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_4373, c_9317])).
% 12.18/4.85  tff(c_9337, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_9326])).
% 12.18/4.85  tff(c_9339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6929, c_9337])).
% 12.18/4.85  tff(c_9340, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4605])).
% 12.18/4.85  tff(c_9456, plain, (![A_653, B_654, C_655]: (k2_relset_1(A_653, B_654, C_655)=k2_relat_1(C_655) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_653, B_654))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.18/4.85  tff(c_11097, plain, (![C_755]: (k2_relset_1('#skF_1', '#skF_1', C_755)=k2_relat_1(C_755) | ~m1_subset_1(C_755, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_9456])).
% 12.18/4.85  tff(c_11106, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4373, c_11097])).
% 12.18/4.85  tff(c_11116, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9340, c_11106])).
% 12.18/4.85  tff(c_11454, plain, (![C_760, A_761, B_762, D_763]: (v2_funct_1(C_760) | ~r2_relset_1(A_761, A_761, k1_partfun1(A_761, B_762, B_762, A_761, C_760, D_763), k6_partfun1(A_761)) | ~m1_subset_1(D_763, k1_zfmisc_1(k2_zfmisc_1(B_762, A_761))) | ~v1_funct_2(D_763, B_762, A_761) | ~v1_funct_1(D_763) | ~m1_subset_1(C_760, k1_zfmisc_1(k2_zfmisc_1(A_761, B_762))) | ~v1_funct_2(C_760, A_761, B_762) | ~v1_funct_1(C_760))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.18/4.85  tff(c_11475, plain, (v2_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_11454])).
% 12.18/4.85  tff(c_11479, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4373, c_4367, c_78, c_76, c_4374, c_4367, c_11475])).
% 12.18/4.85  tff(c_12009, plain, (![C_794, D_795, B_796, A_797]: (k2_funct_1(C_794)=D_795 | k1_xboole_0=B_796 | k1_xboole_0=A_797 | ~v2_funct_1(C_794) | ~r2_relset_1(A_797, A_797, k1_partfun1(A_797, B_796, B_796, A_797, C_794, D_795), k6_partfun1(A_797)) | k2_relset_1(A_797, B_796, C_794)!=B_796 | ~m1_subset_1(D_795, k1_zfmisc_1(k2_zfmisc_1(B_796, A_797))) | ~v1_funct_2(D_795, B_796, A_797) | ~v1_funct_1(D_795) | ~m1_subset_1(C_794, k1_zfmisc_1(k2_zfmisc_1(A_797, B_796))) | ~v1_funct_2(C_794, A_797, B_796) | ~v1_funct_1(C_794))), inference(cnfTransformation, [status(thm)], [f_175])).
% 12.18/4.85  tff(c_12030, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_12009])).
% 12.18/4.85  tff(c_12035, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4373, c_4367, c_78, c_76, c_4374, c_4367, c_11116, c_11479, c_12030])).
% 12.18/4.85  tff(c_12036, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_12035])).
% 12.18/4.85  tff(c_12093, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12036, c_2])).
% 12.18/4.85  tff(c_12095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9590, c_12093])).
% 12.18/4.85  tff(c_12096, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_12035])).
% 12.18/4.85  tff(c_9869, plain, (![A_707, B_708]: (k2_funct_2(A_707, B_708)=k2_funct_1(B_708) | ~m1_subset_1(B_708, k1_zfmisc_1(k2_zfmisc_1(A_707, A_707))) | ~v3_funct_2(B_708, A_707, A_707) | ~v1_funct_2(B_708, A_707, A_707) | ~v1_funct_1(B_708))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.18/4.85  tff(c_12383, plain, (![B_811]: (k2_funct_2('#skF_1', B_811)=k2_funct_1(B_811) | ~m1_subset_1(B_811, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_811, '#skF_1', '#skF_1') | ~v1_funct_2(B_811, '#skF_1', '#skF_1') | ~v1_funct_1(B_811))), inference(superposition, [status(thm), theory('equality')], [c_4367, c_9869])).
% 12.18/4.85  tff(c_12392, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_4373, c_12383])).
% 12.18/4.85  tff(c_12404, plain, (k2_funct_2('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_12096, c_12392])).
% 12.18/4.85  tff(c_12406, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12404, c_68])).
% 12.18/4.85  tff(c_12409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9695, c_12406])).
% 12.18/4.85  tff(c_12411, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_4422])).
% 12.18/4.85  tff(c_12421, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_12411, c_135])).
% 12.18/4.85  tff(c_14, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.18/4.85  tff(c_4388, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4367, c_14])).
% 12.18/4.85  tff(c_4580, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4388])).
% 12.18/4.85  tff(c_12434, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12421, c_4580])).
% 12.18/4.85  tff(c_12450, plain, (![B_7]: (k2_zfmisc_1('#skF_1', B_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12421, c_12421, c_18])).
% 12.18/4.85  tff(c_12600, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12450, c_4367])).
% 12.18/4.85  tff(c_12602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12434, c_12600])).
% 12.18/4.85  tff(c_12604, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4388])).
% 12.18/4.85  tff(c_12650, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_12604, c_10])).
% 12.18/4.85  tff(c_154, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_143])).
% 12.18/4.85  tff(c_265, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_154, c_247])).
% 12.18/4.85  tff(c_339, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_265])).
% 12.18/4.85  tff(c_4370, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_339])).
% 12.18/4.85  tff(c_12695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12650, c_4370])).
% 12.18/4.85  tff(c_12696, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_265])).
% 12.18/4.85  tff(c_12701, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12696, c_72])).
% 12.18/4.85  tff(c_16127, plain, (![A_1074, B_1075, D_1076]: (r2_relset_1(A_1074, B_1075, D_1076, D_1076) | ~m1_subset_1(D_1076, k1_zfmisc_1(k2_zfmisc_1(A_1074, B_1075))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.18/4.85  tff(c_16218, plain, (![D_1089]: (r2_relset_1('#skF_1', '#skF_1', D_1089, D_1089) | ~m1_subset_1(D_1089, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_16127])).
% 12.18/4.85  tff(c_16230, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_12701, c_16218])).
% 12.18/4.85  tff(c_12871, plain, (![C_838, B_839, A_840]: (v1_xboole_0(C_838) | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(B_839, A_840))) | ~v1_xboole_0(A_840))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.18/4.85  tff(c_12874, plain, (![C_838]: (v1_xboole_0(C_838) | ~m1_subset_1(C_838, k1_zfmisc_1('#skF_2')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_12871])).
% 12.18/4.85  tff(c_16166, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_12874])).
% 12.18/4.85  tff(c_12700, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12696, c_80])).
% 12.18/4.85  tff(c_12724, plain, (![C_824, B_825, A_826]: (v5_relat_1(C_824, B_825) | ~m1_subset_1(C_824, k1_zfmisc_1(k2_zfmisc_1(A_826, B_825))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.18/4.85  tff(c_13065, plain, (![C_854]: (v5_relat_1(C_854, '#skF_1') | ~m1_subset_1(C_854, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_12724])).
% 12.18/4.85  tff(c_13082, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_12700, c_13065])).
% 12.18/4.85  tff(c_48, plain, (![B_32, A_31]: (k2_relat_1(B_32)=A_31 | ~v2_funct_2(B_32, A_31) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.18/4.85  tff(c_13092, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_13082, c_48])).
% 12.18/4.85  tff(c_13095, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_13092])).
% 12.18/4.85  tff(c_14589, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_13095])).
% 12.18/4.85  tff(c_14828, plain, (![C_993, B_994, A_995]: (v2_funct_2(C_993, B_994) | ~v3_funct_2(C_993, A_995, B_994) | ~v1_funct_1(C_993) | ~m1_subset_1(C_993, k1_zfmisc_1(k2_zfmisc_1(A_995, B_994))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.18/4.85  tff(c_16081, plain, (![C_1070]: (v2_funct_2(C_1070, '#skF_1') | ~v3_funct_2(C_1070, '#skF_1', '#skF_1') | ~v1_funct_1(C_1070) | ~m1_subset_1(C_1070, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_14828])).
% 12.18/4.85  tff(c_16090, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_12700, c_16081])).
% 12.18/4.85  tff(c_16101, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_16090])).
% 12.18/4.85  tff(c_16103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14589, c_16101])).
% 12.18/4.85  tff(c_16104, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_13095])).
% 12.18/4.85  tff(c_16183, plain, (![A_1085, B_1086, C_1087]: (k2_relset_1(A_1085, B_1086, C_1087)=k2_relat_1(C_1087) | ~m1_subset_1(C_1087, k1_zfmisc_1(k2_zfmisc_1(A_1085, B_1086))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.18/4.85  tff(c_16315, plain, (![C_1101]: (k2_relset_1('#skF_1', '#skF_1', C_1101)=k2_relat_1(C_1101) | ~m1_subset_1(C_1101, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_16183])).
% 12.18/4.85  tff(c_16324, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12700, c_16315])).
% 12.18/4.85  tff(c_16334, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16104, c_16324])).
% 12.18/4.85  tff(c_16241, plain, (![C_1092, A_1093, B_1094]: (v2_funct_1(C_1092) | ~v3_funct_2(C_1092, A_1093, B_1094) | ~v1_funct_1(C_1092) | ~m1_subset_1(C_1092, k1_zfmisc_1(k2_zfmisc_1(A_1093, B_1094))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.18/4.85  tff(c_16428, plain, (![C_1113]: (v2_funct_1(C_1113) | ~v3_funct_2(C_1113, '#skF_1', '#skF_1') | ~v1_funct_1(C_1113) | ~m1_subset_1(C_1113, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_16241])).
% 12.18/4.85  tff(c_16437, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_12700, c_16428])).
% 12.18/4.85  tff(c_16448, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_16437])).
% 12.18/4.85  tff(c_18924, plain, (![C_1227, D_1228, B_1229, A_1230]: (k2_funct_1(C_1227)=D_1228 | k1_xboole_0=B_1229 | k1_xboole_0=A_1230 | ~v2_funct_1(C_1227) | ~r2_relset_1(A_1230, A_1230, k1_partfun1(A_1230, B_1229, B_1229, A_1230, C_1227, D_1228), k6_partfun1(A_1230)) | k2_relset_1(A_1230, B_1229, C_1227)!=B_1229 | ~m1_subset_1(D_1228, k1_zfmisc_1(k2_zfmisc_1(B_1229, A_1230))) | ~v1_funct_2(D_1228, B_1229, A_1230) | ~v1_funct_1(D_1228) | ~m1_subset_1(C_1227, k1_zfmisc_1(k2_zfmisc_1(A_1230, B_1229))) | ~v1_funct_2(C_1227, A_1230, B_1229) | ~v1_funct_1(C_1227))), inference(cnfTransformation, [status(thm)], [f_175])).
% 12.18/4.85  tff(c_18945, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_18924])).
% 12.18/4.85  tff(c_18950, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_12700, c_12696, c_78, c_76, c_12701, c_12696, c_16334, c_16448, c_18945])).
% 12.18/4.85  tff(c_18951, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18950])).
% 12.18/4.85  tff(c_19009, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18951, c_2])).
% 12.18/4.85  tff(c_19011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16166, c_19009])).
% 12.18/4.85  tff(c_19012, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_18950])).
% 12.18/4.85  tff(c_16955, plain, (![A_1136, B_1137]: (k2_funct_2(A_1136, B_1137)=k2_funct_1(B_1137) | ~m1_subset_1(B_1137, k1_zfmisc_1(k2_zfmisc_1(A_1136, A_1136))) | ~v3_funct_2(B_1137, A_1136, A_1136) | ~v1_funct_2(B_1137, A_1136, A_1136) | ~v1_funct_1(B_1137))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.18/4.85  tff(c_18333, plain, (![B_1199]: (k2_funct_2('#skF_1', B_1199)=k2_funct_1(B_1199) | ~m1_subset_1(B_1199, k1_zfmisc_1('#skF_2')) | ~v3_funct_2(B_1199, '#skF_1', '#skF_1') | ~v1_funct_2(B_1199, '#skF_1', '#skF_1') | ~v1_funct_1(B_1199))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_16955])).
% 12.18/4.85  tff(c_18342, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_12700, c_18333])).
% 12.18/4.85  tff(c_18354, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_18342])).
% 12.18/4.85  tff(c_18360, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18354, c_68])).
% 12.18/4.85  tff(c_19014, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19012, c_18360])).
% 12.18/4.85  tff(c_19018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16230, c_19014])).
% 12.18/4.85  tff(c_19020, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_12874])).
% 12.18/4.85  tff(c_19030, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_19020, c_135])).
% 12.18/4.85  tff(c_12712, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_12696, c_14])).
% 12.18/4.85  tff(c_12826, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_12712])).
% 12.18/4.85  tff(c_19044, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19030, c_12826])).
% 12.18/4.85  tff(c_16, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.18/4.85  tff(c_19055, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19030, c_19030, c_16])).
% 12.18/4.85  tff(c_19190, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19055, c_12696])).
% 12.18/4.85  tff(c_19192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19044, c_19190])).
% 12.18/4.85  tff(c_19194, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_12712])).
% 12.18/4.85  tff(c_19209, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_19194, c_10])).
% 12.18/4.85  tff(c_12698, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12696, c_155])).
% 12.18/4.85  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.18/4.85  tff(c_12723, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12698, c_4])).
% 12.18/4.85  tff(c_12774, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_12723])).
% 12.18/4.85  tff(c_19235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19209, c_12774])).
% 12.18/4.85  tff(c_19236, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_12723])).
% 12.18/4.85  tff(c_19239, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19236, c_12701])).
% 12.18/4.85  tff(c_19242, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19236, c_12696])).
% 12.18/4.85  tff(c_19486, plain, (![A_1258, B_1259, D_1260]: (r2_relset_1(A_1258, B_1259, D_1260, D_1260) | ~m1_subset_1(D_1260, k1_zfmisc_1(k2_zfmisc_1(A_1258, B_1259))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.18/4.85  tff(c_22114, plain, (![D_1441]: (r2_relset_1('#skF_1', '#skF_1', D_1441, D_1441) | ~m1_subset_1(D_1441, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_19242, c_19486])).
% 12.18/4.85  tff(c_22124, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_19239, c_22114])).
% 12.18/4.85  tff(c_74, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.18/4.85  tff(c_19337, plain, (![C_1247, B_1248, A_1249]: (v1_xboole_0(C_1247) | ~m1_subset_1(C_1247, k1_zfmisc_1(k2_zfmisc_1(B_1248, A_1249))) | ~v1_xboole_0(A_1249))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.18/4.85  tff(c_19340, plain, (![C_1247]: (v1_xboole_0(C_1247) | ~m1_subset_1(C_1247, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19242, c_19337])).
% 12.18/4.85  tff(c_22028, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_19340])).
% 12.18/4.85  tff(c_194, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_173])).
% 12.18/4.85  tff(c_12727, plain, (![C_824]: (v5_relat_1(C_824, '#skF_1') | ~m1_subset_1(C_824, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_12724])).
% 12.18/4.85  tff(c_19600, plain, (![C_1276]: (v5_relat_1(C_1276, '#skF_1') | ~m1_subset_1(C_1276, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_19236, c_12727])).
% 12.18/4.85  tff(c_19613, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_19239, c_19600])).
% 12.18/4.85  tff(c_19617, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_19613, c_48])).
% 12.18/4.85  tff(c_19620, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_19617])).
% 12.18/4.85  tff(c_19626, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_19620])).
% 12.18/4.85  tff(c_19244, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_19236, c_70])).
% 12.18/4.85  tff(c_21837, plain, (![D_1401, A_1402, B_1403, C_1404]: (v2_funct_2(D_1401, A_1402) | ~r2_relset_1(A_1402, A_1402, k1_partfun1(A_1402, B_1403, B_1403, A_1402, C_1404, D_1401), k6_partfun1(A_1402)) | ~m1_subset_1(D_1401, k1_zfmisc_1(k2_zfmisc_1(B_1403, A_1402))) | ~v1_funct_2(D_1401, B_1403, A_1402) | ~v1_funct_1(D_1401) | ~m1_subset_1(C_1404, k1_zfmisc_1(k2_zfmisc_1(A_1402, B_1403))) | ~v1_funct_2(C_1404, A_1402, B_1403) | ~v1_funct_1(C_1404))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.18/4.85  tff(c_21855, plain, (v2_funct_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_19244, c_21837])).
% 12.18/4.85  tff(c_21861, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_19239, c_19242, c_21855])).
% 12.18/4.85  tff(c_21863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19626, c_21861])).
% 12.18/4.85  tff(c_21864, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_19620])).
% 12.18/4.85  tff(c_21916, plain, (![A_1411, B_1412, C_1413]: (k2_relset_1(A_1411, B_1412, C_1413)=k2_relat_1(C_1413) | ~m1_subset_1(C_1413, k1_zfmisc_1(k2_zfmisc_1(A_1411, B_1412))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.18/4.85  tff(c_23887, plain, (![C_1514]: (k2_relset_1('#skF_1', '#skF_1', C_1514)=k2_relat_1(C_1514) | ~m1_subset_1(C_1514, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_19242, c_21916])).
% 12.18/4.85  tff(c_23893, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_19239, c_23887])).
% 12.18/4.85  tff(c_23901, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21864, c_23893])).
% 12.18/4.85  tff(c_24023, plain, (![C_1522, A_1523, B_1524, D_1525]: (v2_funct_1(C_1522) | ~r2_relset_1(A_1523, A_1523, k1_partfun1(A_1523, B_1524, B_1524, A_1523, C_1522, D_1525), k6_partfun1(A_1523)) | ~m1_subset_1(D_1525, k1_zfmisc_1(k2_zfmisc_1(B_1524, A_1523))) | ~v1_funct_2(D_1525, B_1524, A_1523) | ~v1_funct_1(D_1525) | ~m1_subset_1(C_1522, k1_zfmisc_1(k2_zfmisc_1(A_1523, B_1524))) | ~v1_funct_2(C_1522, A_1523, B_1524) | ~v1_funct_1(C_1522))), inference(cnfTransformation, [status(thm)], [f_150])).
% 12.18/4.85  tff(c_24041, plain, (v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_19244, c_24023])).
% 12.18/4.85  tff(c_24047, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_19239, c_19242, c_24041])).
% 12.18/4.85  tff(c_25201, plain, (![C_1557, D_1558, B_1559, A_1560]: (k2_funct_1(C_1557)=D_1558 | k1_xboole_0=B_1559 | k1_xboole_0=A_1560 | ~v2_funct_1(C_1557) | ~r2_relset_1(A_1560, A_1560, k1_partfun1(A_1560, B_1559, B_1559, A_1560, C_1557, D_1558), k6_partfun1(A_1560)) | k2_relset_1(A_1560, B_1559, C_1557)!=B_1559 | ~m1_subset_1(D_1558, k1_zfmisc_1(k2_zfmisc_1(B_1559, A_1560))) | ~v1_funct_2(D_1558, B_1559, A_1560) | ~v1_funct_1(D_1558) | ~m1_subset_1(C_1557, k1_zfmisc_1(k2_zfmisc_1(A_1560, B_1559))) | ~v1_funct_2(C_1557, A_1560, B_1559) | ~v1_funct_1(C_1557))), inference(cnfTransformation, [status(thm)], [f_175])).
% 12.18/4.85  tff(c_25222, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_19244, c_25201])).
% 12.18/4.85  tff(c_25228, plain, (k2_funct_1('#skF_3')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_19239, c_19242, c_23901, c_24047, c_25222])).
% 12.18/4.85  tff(c_25231, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_25228])).
% 12.18/4.85  tff(c_25292, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25231, c_2])).
% 12.18/4.85  tff(c_25294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22028, c_25292])).
% 12.18/4.85  tff(c_25295, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_25228])).
% 12.18/4.85  tff(c_22643, plain, (![A_1467, B_1468]: (k2_funct_2(A_1467, B_1468)=k2_funct_1(B_1468) | ~m1_subset_1(B_1468, k1_zfmisc_1(k2_zfmisc_1(A_1467, A_1467))) | ~v3_funct_2(B_1468, A_1467, A_1467) | ~v1_funct_2(B_1468, A_1467, A_1467) | ~v1_funct_1(B_1468))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.18/4.85  tff(c_26116, plain, (![B_1574]: (k2_funct_2('#skF_1', B_1574)=k2_funct_1(B_1574) | ~m1_subset_1(B_1574, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_1574, '#skF_1', '#skF_1') | ~v1_funct_2(B_1574, '#skF_1', '#skF_1') | ~v1_funct_1(B_1574))), inference(superposition, [status(thm), theory('equality')], [c_19242, c_22643])).
% 12.18/4.85  tff(c_26122, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_19239, c_26116])).
% 12.18/4.85  tff(c_26131, plain, (k2_funct_2('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_25295, c_26122])).
% 12.18/4.85  tff(c_19246, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_19236, c_68])).
% 12.18/4.85  tff(c_26133, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26131, c_19246])).
% 12.18/4.85  tff(c_26136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22124, c_26133])).
% 12.18/4.85  tff(c_26138, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_19340])).
% 12.18/4.85  tff(c_26151, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26138, c_135])).
% 12.18/4.85  tff(c_19335, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19236, c_12712])).
% 12.18/4.85  tff(c_19336, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_19335])).
% 12.18/4.85  tff(c_26169, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26151, c_19336])).
% 12.18/4.85  tff(c_26181, plain, (![B_7]: (k2_zfmisc_1('#skF_1', B_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26151, c_26151, c_18])).
% 12.18/4.85  tff(c_26366, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26181, c_19242])).
% 12.18/4.85  tff(c_26368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26169, c_26366])).
% 12.18/4.85  tff(c_26370, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_19335])).
% 12.18/4.85  tff(c_26369, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_19335])).
% 12.18/4.85  tff(c_26539, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26370, c_26370, c_26369])).
% 12.18/4.85  tff(c_26540, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_26539])).
% 12.18/4.85  tff(c_26385, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_26370, c_10])).
% 12.18/4.85  tff(c_26562, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_26540, c_26385])).
% 12.18/4.85  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.18/4.85  tff(c_26625, plain, (![A_1598, B_1599, D_1600]: (r2_relset_1(A_1598, B_1599, D_1600, D_1600) | ~m1_subset_1(D_1600, k1_zfmisc_1(k2_zfmisc_1(A_1598, B_1599))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.18/4.85  tff(c_30202, plain, (![A_1847, B_1848, A_1849]: (r2_relset_1(A_1847, B_1848, A_1849, A_1849) | ~r1_tarski(A_1849, k2_zfmisc_1(A_1847, B_1848)))), inference(resolution, [status(thm)], [c_22, c_26625])).
% 12.18/4.85  tff(c_30219, plain, (![A_1847, B_1848]: (r2_relset_1(A_1847, B_1848, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_26562, c_30202])).
% 12.18/4.85  tff(c_26578, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26540, c_78])).
% 12.18/4.85  tff(c_156, plain, (![A_68]: (m1_subset_1(k6_partfun1(A_68), k1_zfmisc_1(k2_zfmisc_1(A_68, A_68))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.18/4.85  tff(c_163, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_156])).
% 12.18/4.85  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.18/4.85  tff(c_172, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_163, c_20])).
% 12.18/4.85  tff(c_251, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_172, c_247])).
% 12.18/4.85  tff(c_263, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_251])).
% 12.18/4.85  tff(c_26377, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26370, c_26370, c_263])).
% 12.18/4.85  tff(c_26561, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26540, c_26540, c_26377])).
% 12.18/4.85  tff(c_26576, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26540, c_76])).
% 12.18/4.85  tff(c_26577, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26540, c_74])).
% 12.18/4.85  tff(c_60, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.18/4.85  tff(c_24, plain, (![A_10]: (k2_funct_1(k6_relat_1(A_10))=k6_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.18/4.85  tff(c_87, plain, (![A_10]: (k2_funct_1(k6_partfun1(A_10))=k6_partfun1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_24])).
% 12.18/4.85  tff(c_29228, plain, (![A_1763, B_1764]: (k2_funct_2(A_1763, B_1764)=k2_funct_1(B_1764) | ~m1_subset_1(B_1764, k1_zfmisc_1(k2_zfmisc_1(A_1763, A_1763))) | ~v3_funct_2(B_1764, A_1763, A_1763) | ~v1_funct_2(B_1764, A_1763, A_1763) | ~v1_funct_1(B_1764))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.18/4.85  tff(c_29239, plain, (![A_39]: (k2_funct_2(A_39, k6_partfun1(A_39))=k2_funct_1(k6_partfun1(A_39)) | ~v3_funct_2(k6_partfun1(A_39), A_39, A_39) | ~v1_funct_2(k6_partfun1(A_39), A_39, A_39) | ~v1_funct_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_56, c_29228])).
% 12.18/4.85  tff(c_33772, plain, (![A_1955]: (k2_funct_2(A_1955, k6_partfun1(A_1955))=k6_partfun1(A_1955) | ~v3_funct_2(k6_partfun1(A_1955), A_1955, A_1955) | ~v1_funct_2(k6_partfun1(A_1955), A_1955, A_1955) | ~v1_funct_1(k6_partfun1(A_1955)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_29239])).
% 12.18/4.85  tff(c_33796, plain, (k2_funct_2('#skF_1', k6_partfun1('#skF_1'))=k6_partfun1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2(k6_partfun1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26561, c_33772])).
% 12.18/4.85  tff(c_33798, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26578, c_26561, c_26576, c_26561, c_26577, c_26561, c_26561, c_33796])).
% 12.18/4.85  tff(c_26572, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26540, c_26540, c_19246])).
% 12.18/4.85  tff(c_33799, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33798, c_26572])).
% 12.18/4.85  tff(c_33802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30219, c_33799])).
% 12.18/4.85  tff(c_33803, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_26539])).
% 12.18/4.85  tff(c_33804, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_26539])).
% 12.18/4.85  tff(c_33835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33803, c_33804])).
% 12.18/4.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.18/4.85  
% 12.18/4.85  Inference rules
% 12.18/4.85  ----------------------
% 12.18/4.85  #Ref     : 0
% 12.18/4.85  #Sup     : 8335
% 12.18/4.85  #Fact    : 0
% 12.18/4.85  #Define  : 0
% 12.18/4.85  #Split   : 58
% 12.18/4.85  #Chain   : 0
% 12.18/4.85  #Close   : 0
% 12.18/4.85  
% 12.18/4.85  Ordering : KBO
% 12.18/4.85  
% 12.18/4.85  Simplification rules
% 12.18/4.85  ----------------------
% 12.18/4.85  #Subsume      : 1020
% 12.18/4.85  #Demod        : 8359
% 12.18/4.85  #Tautology    : 4702
% 12.18/4.85  #SimpNegUnit  : 19
% 12.18/4.85  #BackRed      : 506
% 12.18/4.85  
% 12.18/4.85  #Partial instantiations: 0
% 12.18/4.85  #Strategies tried      : 1
% 12.18/4.85  
% 12.18/4.85  Timing (in seconds)
% 12.18/4.85  ----------------------
% 12.18/4.85  Preprocessing        : 0.37
% 12.18/4.85  Parsing              : 0.19
% 12.18/4.85  CNF conversion       : 0.02
% 12.18/4.85  Main loop            : 3.65
% 12.18/4.85  Inferencing          : 1.05
% 12.18/4.85  Reduction            : 1.38
% 12.18/4.85  Demodulation         : 1.02
% 12.18/4.85  BG Simplification    : 0.11
% 12.18/4.85  Subsumption          : 0.86
% 12.18/4.85  Abstraction          : 0.13
% 12.18/4.85  MUC search           : 0.00
% 12.18/4.85  Cooper               : 0.00
% 12.18/4.85  Total                : 4.12
% 12.18/4.85  Index Insertion      : 0.00
% 12.18/4.85  Index Deletion       : 0.00
% 12.18/4.85  Index Matching       : 0.00
% 12.18/4.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
