%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:55 EST 2020

% Result     : Theorem 6.53s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :  239 (3589 expanded)
%              Number of leaves         :   48 (1184 expanded)
%              Depth                    :   20
%              Number of atoms          :  466 (8821 expanded)
%              Number of equality atoms :  200 (3347 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_46,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1381,plain,(
    ! [A_153,B_154,D_155] :
      ( r2_relset_1(A_153,B_154,D_155,D_155)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1392,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1381])).

tff(c_50,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_16,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_153,plain,(
    ! [A_50] :
      ( k2_relat_1(A_50) != k1_xboole_0
      | k1_xboole_0 = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_6] :
      ( k2_relat_1(k6_partfun1(A_6)) != k1_xboole_0
      | k6_partfun1(A_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_79,c_153])).

tff(c_165,plain,(
    ! [A_6] :
      ( k1_xboole_0 != A_6
      | k6_partfun1(A_6) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_159])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_334,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_60])).

tff(c_358,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_76,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_74,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_280,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_298,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_280])).

tff(c_307,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_323,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_307])).

tff(c_409,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(B_75) = A_76
      | ~ v2_funct_2(B_75,A_76)
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_418,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_323,c_409])).

tff(c_430,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_418])).

tff(c_434,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_72,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1012,plain,(
    ! [C_124,B_125,A_126] :
      ( v2_funct_2(C_124,B_125)
      | ~ v3_funct_2(C_124,A_126,B_125)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1024,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1012])).

tff(c_1033,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1024])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_1033])).

tff(c_1036,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_1394,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1406,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1394])).

tff(c_1414,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1406])).

tff(c_1446,plain,(
    ! [C_161,A_162,B_163] :
      ( v2_funct_1(C_161)
      | ~ v3_funct_2(C_161,A_162,B_163)
      | ~ v1_funct_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1458,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1446])).

tff(c_1468,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_1458])).

tff(c_2094,plain,(
    ! [C_204,D_205,B_206,A_207] :
      ( k2_funct_1(C_204) = D_205
      | k1_xboole_0 = B_206
      | k1_xboole_0 = A_207
      | ~ v2_funct_1(C_204)
      | ~ r2_relset_1(A_207,A_207,k1_partfun1(A_207,B_206,B_206,A_207,C_204,D_205),k6_partfun1(A_207))
      | k2_relset_1(A_207,B_206,C_204) != B_206
      | ~ m1_subset_1(D_205,k1_zfmisc_1(k2_zfmisc_1(B_206,A_207)))
      | ~ v1_funct_2(D_205,B_206,A_207)
      | ~ v1_funct_1(D_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206)))
      | ~ v1_funct_2(C_204,A_207,B_206)
      | ~ v1_funct_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2100,plain,
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
    inference(resolution,[status(thm)],[c_60,c_2094])).

tff(c_2106,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_62,c_1414,c_1468,c_2100])).

tff(c_2107,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_2106])).

tff(c_1716,plain,(
    ! [A_182,B_183] :
      ( k2_funct_2(A_182,B_183) = k2_funct_1(B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_zfmisc_1(A_182,A_182)))
      | ~ v3_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1728,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1716])).

tff(c_1736,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1728])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1741,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1736,c_58])).

tff(c_2108,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2107,c_1741])).

tff(c_2112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_2108])).

tff(c_2114,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_6,plain,(
    ! [A_4] :
      ( k2_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_331,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_298,c_6])).

tff(c_340,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_2115,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2114,c_340])).

tff(c_2684,plain,(
    ! [B_244,A_245] :
      ( k2_relat_1(B_244) = A_245
      | ~ v2_funct_2(B_244,A_245)
      | ~ v5_relat_1(B_244,A_245)
      | ~ v1_relat_1(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2693,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_323,c_2684])).

tff(c_2702,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_2693])).

tff(c_2703,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2115,c_2702])).

tff(c_2938,plain,(
    ! [C_265,B_266,A_267] :
      ( v2_funct_2(C_265,B_266)
      | ~ v3_funct_2(C_265,A_267,B_266)
      | ~ v1_funct_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2947,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_2938])).

tff(c_2955,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_2947])).

tff(c_2957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2703,c_2955])).

tff(c_2958,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_99,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_14])).

tff(c_10,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [A_48] : k1_relat_1(k6_partfun1(A_48)) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_142,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_133])).

tff(c_2969,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_2958,c_142])).

tff(c_8,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_330,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_298,c_8])).

tff(c_339,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_2960,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_339])).

tff(c_3007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2969,c_2960])).

tff(c_3008,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_3114,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_2')
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_334])).

tff(c_3115,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3114])).

tff(c_117,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_80])).

tff(c_3036,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_117])).

tff(c_3171,plain,(
    ! [B_280,A_281] :
      ( k2_relat_1(B_280) = A_281
      | ~ v2_funct_2(B_280,A_281)
      | ~ v5_relat_1(B_280,A_281)
      | ~ v1_relat_1(B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3180,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_323,c_3171])).

tff(c_3192,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_3036,c_3180])).

tff(c_3193,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_3192])).

tff(c_3472,plain,(
    ! [C_301,B_302,A_303] :
      ( v2_funct_2(C_301,B_302)
      | ~ v3_funct_2(C_301,A_303,B_302)
      | ~ v1_funct_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3484,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3472])).

tff(c_3495,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_3484])).

tff(c_3497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3193,c_3495])).

tff(c_3499,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3114])).

tff(c_3508,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3008])).

tff(c_191,plain,(
    ! [A_52] :
      ( k1_xboole_0 != A_52
      | k6_partfun1(A_52) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_159])).

tff(c_46,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_197,plain,(
    ! [A_52] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | k1_xboole_0 != A_52 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_46])).

tff(c_4093,plain,(
    ! [A_347] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_347,A_347)))
      | A_347 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_3508,c_197])).

tff(c_30,plain,(
    ! [A_19,B_20,D_22] :
      ( r2_relset_1(A_19,B_20,D_22,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4144,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4093,c_30])).

tff(c_3514,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_74])).

tff(c_3515,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_72])).

tff(c_3516,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_76])).

tff(c_3031,plain,(
    ! [A_6] :
      ( A_6 != '#skF_2'
      | k6_partfun1(A_6) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_165])).

tff(c_3908,plain,(
    ! [A_6] :
      ( A_6 != '#skF_1'
      | k6_partfun1(A_6) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3031])).

tff(c_3511,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_298])).

tff(c_18,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_6] : v2_funct_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_124,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_78])).

tff(c_3037,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_124])).

tff(c_3507,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3037])).

tff(c_3503,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3036])).

tff(c_3909,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3031])).

tff(c_3035,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_142])).

tff(c_3504,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3035])).

tff(c_122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_79])).

tff(c_166,plain,(
    ! [A_51] :
      ( k8_relat_1(k2_relat_1(A_51),A_51) = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_166])).

tff(c_182,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_175])).

tff(c_3032,plain,(
    k8_relat_1('#skF_2','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_3008,c_182])).

tff(c_3635,plain,(
    k8_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3499,c_3032])).

tff(c_3039,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_14])).

tff(c_3505,plain,(
    k6_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3039])).

tff(c_3538,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_3505])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_partfun1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_4157,plain,(
    ! [B_352] :
      ( k8_relat_1('#skF_1',B_352) = k5_relat_1(B_352,'#skF_1')
      | ~ v1_relat_1(B_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3538,c_82])).

tff(c_4160,plain,(
    k8_relat_1('#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3511,c_4157])).

tff(c_4165,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_4160])).

tff(c_3911,plain,(
    ! [A_332] :
      ( A_332 != '#skF_1'
      | k6_partfun1(A_332) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3031])).

tff(c_4237,plain,(
    ! [A_359,B_360] :
      ( k8_relat_1(A_359,B_360) = k5_relat_1(B_360,'#skF_1')
      | ~ v1_relat_1(B_360)
      | A_359 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_82])).

tff(c_4239,plain,(
    ! [A_359] :
      ( k8_relat_1(A_359,'#skF_1') = k5_relat_1('#skF_1','#skF_1')
      | A_359 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3511,c_4237])).

tff(c_4243,plain,(
    ! [A_359] :
      ( k8_relat_1(A_359,'#skF_1') = '#skF_1'
      | A_359 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_4239])).

tff(c_81,plain,(
    ! [A_5] : k1_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_20,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4549,plain,(
    ! [A_372,B_373] :
      ( k2_funct_1(A_372) = B_373
      | k6_partfun1(k1_relat_1(A_372)) != k5_relat_1(A_372,B_373)
      | k2_relat_1(A_372) != k1_relat_1(B_373)
      | ~ v2_funct_1(A_372)
      | ~ v1_funct_1(B_373)
      | ~ v1_relat_1(B_373)
      | ~ v1_funct_1(A_372)
      | ~ v1_relat_1(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_4559,plain,(
    ! [A_1,B_2] :
      ( k6_partfun1(A_1) = k2_funct_1(B_2)
      | k8_relat_1(A_1,B_2) != k6_partfun1(k1_relat_1(B_2))
      | k2_relat_1(B_2) != k1_relat_1(k6_partfun1(A_1))
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(k6_partfun1(A_1))
      | ~ v1_relat_1(k6_partfun1(A_1))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4549])).

tff(c_5720,plain,(
    ! [A_433,B_434] :
      ( k6_partfun1(A_433) = k2_funct_1(B_434)
      | k8_relat_1(A_433,B_434) != k6_partfun1(k1_relat_1(B_434))
      | k2_relat_1(B_434) != A_433
      | ~ v2_funct_1(B_434)
      | ~ v1_funct_1(k6_partfun1(A_433))
      | ~ v1_funct_1(B_434)
      | ~ v1_relat_1(B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_81,c_4559])).

tff(c_5747,plain,(
    ! [A_359] :
      ( k6_partfun1(A_359) = k2_funct_1('#skF_1')
      | k6_partfun1(k1_relat_1('#skF_1')) != '#skF_1'
      | k2_relat_1('#skF_1') != A_359
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_359))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1')
      | A_359 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4243,c_5720])).

tff(c_5784,plain,(
    ! [A_435] :
      ( k6_partfun1(A_435) = k2_funct_1('#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_435))
      | A_435 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3511,c_3516,c_3507,c_3503,c_3909,c_3504,c_5747])).

tff(c_5802,plain,(
    ! [A_6] :
      ( k6_partfun1(A_6) = k2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1'
      | A_6 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3908,c_5784])).

tff(c_5806,plain,(
    ! [A_436] :
      ( k6_partfun1(A_436) = k2_funct_1('#skF_1')
      | A_436 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3516,c_5802])).

tff(c_6018,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_80])).

tff(c_178,plain,(
    ! [A_5] :
      ( k8_relat_1(A_5,k6_partfun1(A_5)) = k6_partfun1(A_5)
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_166])).

tff(c_184,plain,(
    ! [A_5] : k8_relat_1(A_5,k6_partfun1(A_5)) = k6_partfun1(A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_178])).

tff(c_4561,plain,(
    ! [A_5,B_373] :
      ( k2_funct_1(k6_partfun1(A_5)) = B_373
      | k5_relat_1(k6_partfun1(A_5),B_373) != k6_partfun1(A_5)
      | k2_relat_1(k6_partfun1(A_5)) != k1_relat_1(B_373)
      | ~ v2_funct_1(k6_partfun1(A_5))
      | ~ v1_funct_1(B_373)
      | ~ v1_relat_1(B_373)
      | ~ v1_funct_1(k6_partfun1(A_5))
      | ~ v1_relat_1(k6_partfun1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4549])).

tff(c_5460,plain,(
    ! [A_427,B_428] :
      ( k2_funct_1(k6_partfun1(A_427)) = B_428
      | k5_relat_1(k6_partfun1(A_427),B_428) != k6_partfun1(A_427)
      | k1_relat_1(B_428) != A_427
      | ~ v1_funct_1(B_428)
      | ~ v1_relat_1(B_428)
      | ~ v1_funct_1(k6_partfun1(A_427)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_80,c_4561])).

tff(c_5481,plain,(
    ! [A_1,A_427] :
      ( k6_partfun1(A_1) = k2_funct_1(k6_partfun1(A_427))
      | k8_relat_1(A_1,k6_partfun1(A_427)) != k6_partfun1(A_427)
      | k1_relat_1(k6_partfun1(A_1)) != A_427
      | ~ v1_funct_1(k6_partfun1(A_1))
      | ~ v1_relat_1(k6_partfun1(A_1))
      | ~ v1_funct_1(k6_partfun1(A_427))
      | ~ v1_relat_1(k6_partfun1(A_427)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_5460])).

tff(c_5495,plain,(
    ! [A_429] :
      ( k2_funct_1(k6_partfun1(A_429)) = k6_partfun1(A_429)
      | ~ v1_funct_1(k6_partfun1(A_429)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_79,c_79,c_81,c_5481])).

tff(c_5510,plain,(
    ! [A_6] :
      ( k2_funct_1(k6_partfun1(A_6)) = k6_partfun1(A_6)
      | ~ v1_funct_1('#skF_1')
      | A_6 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3908,c_5495])).

tff(c_5514,plain,(
    ! [A_430] :
      ( k2_funct_1(k6_partfun1(A_430)) = k6_partfun1(A_430)
      | A_430 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3516,c_5510])).

tff(c_5539,plain,(
    ! [A_431] :
      ( k6_partfun1(A_431) = k2_funct_1('#skF_1')
      | A_431 != '#skF_1'
      | A_431 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3908,c_5514])).

tff(c_5663,plain,(
    ! [A_431] :
      ( v1_relat_1(k2_funct_1('#skF_1'))
      | A_431 != '#skF_1'
      | A_431 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5539,c_79])).

tff(c_5688,plain,(
    ! [A_431] :
      ( A_431 != '#skF_1'
      | A_431 != '#skF_1' ) ),
    inference(splitLeft,[status(thm)],[c_5663])).

tff(c_5694,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5688])).

tff(c_5695,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5663])).

tff(c_3033,plain,(
    ! [A_4] :
      ( k2_relat_1(A_4) != '#skF_2'
      | A_4 = '#skF_2'
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3008,c_3008,c_6])).

tff(c_4006,plain,(
    ! [A_4] :
      ( k2_relat_1(A_4) != '#skF_1'
      | A_4 = '#skF_1'
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_3499,c_3033])).

tff(c_5710,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5695,c_4006])).

tff(c_5782,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5710])).

tff(c_6021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6018,c_5782])).

tff(c_6022,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5710])).

tff(c_4090,plain,(
    ! [A_52] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | A_52 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_3508,c_197])).

tff(c_4329,plain,(
    ! [A_365,B_366] :
      ( k2_funct_2(A_365,B_366) = k2_funct_1(B_366)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(k2_zfmisc_1(A_365,A_365)))
      | ~ v3_funct_2(B_366,A_365,A_365)
      | ~ v1_funct_2(B_366,A_365,A_365)
      | ~ v1_funct_1(B_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4332,plain,(
    ! [A_52] :
      ( k2_funct_2(A_52,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_1('#skF_1')
      | A_52 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_4090,c_4329])).

tff(c_4338,plain,(
    ! [A_52] :
      ( k2_funct_2(A_52,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_52,A_52)
      | ~ v1_funct_2('#skF_1',A_52,A_52)
      | A_52 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3516,c_4332])).

tff(c_6459,plain,(
    ! [A_463] :
      ( k2_funct_2(A_463,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_463,A_463)
      | ~ v1_funct_2('#skF_1',A_463,A_463)
      | A_463 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6022,c_4338])).

tff(c_6462,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3515,c_6459])).

tff(c_6465,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3514,c_6462])).

tff(c_297,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_280])).

tff(c_306,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_297,c_6])).

tff(c_3724,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_3508,c_306])).

tff(c_3725,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3724])).

tff(c_322,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_307])).

tff(c_3596,plain,(
    ! [B_305,A_306] :
      ( k2_relat_1(B_305) = A_306
      | ~ v2_funct_2(B_305,A_306)
      | ~ v5_relat_1(B_305,A_306)
      | ~ v1_relat_1(B_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3605,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_322,c_3596])).

tff(c_3614,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_3605])).

tff(c_3796,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3725,c_3614])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3799,plain,(
    ! [C_324,B_325,A_326] :
      ( v2_funct_2(C_324,B_325)
      | ~ v3_funct_2(C_324,A_326,B_325)
      | ~ v1_funct_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3808,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_3799])).

tff(c_3816,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_3808])).

tff(c_3818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3796,c_3816])).

tff(c_3819,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3724])).

tff(c_305,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_297,c_8])).

tff(c_3644,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_3508,c_305])).

tff(c_3645,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3644])).

tff(c_3821,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3819,c_3645])).

tff(c_3832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3504,c_3821])).

tff(c_3833,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3644])).

tff(c_3512,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_58])).

tff(c_3998,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3833,c_3512])).

tff(c_6466,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6465,c_3998])).

tff(c_6469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4144,c_6466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.53/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.36  
% 6.53/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.36  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k8_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.53/2.36  
% 6.53/2.36  %Foreground sorts:
% 6.53/2.36  
% 6.53/2.36  
% 6.53/2.36  %Background operators:
% 6.53/2.36  
% 6.53/2.36  
% 6.53/2.36  %Foreground operators:
% 6.53/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.53/2.36  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.53/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.53/2.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.53/2.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.53/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.53/2.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.53/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.53/2.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.53/2.36  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.53/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.53/2.36  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.53/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.53/2.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.53/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.53/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.53/2.36  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.53/2.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.53/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.53/2.36  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.53/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.53/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.53/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.53/2.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.53/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.53/2.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.53/2.36  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.53/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.53/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.53/2.36  
% 6.88/2.40  tff(f_191, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 6.88/2.40  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.88/2.40  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.88/2.40  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.88/2.40  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.88/2.40  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.88/2.40  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.88/2.40  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.88/2.40  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.88/2.40  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.88/2.40  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.88/2.40  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.88/2.40  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.88/2.40  tff(f_46, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.88/2.40  tff(f_113, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.88/2.40  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 6.88/2.40  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 6.88/2.40  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.88/2.40  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_1381, plain, (![A_153, B_154, D_155]: (r2_relset_1(A_153, B_154, D_155, D_155) | ~m1_subset_1(D_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.88/2.40  tff(c_1392, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_1381])).
% 6.88/2.40  tff(c_50, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.88/2.40  tff(c_12, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.88/2.40  tff(c_80, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 6.88/2.40  tff(c_16, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.88/2.40  tff(c_79, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 6.88/2.40  tff(c_153, plain, (![A_50]: (k2_relat_1(A_50)!=k1_xboole_0 | k1_xboole_0=A_50 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.88/2.40  tff(c_159, plain, (![A_6]: (k2_relat_1(k6_partfun1(A_6))!=k1_xboole_0 | k6_partfun1(A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_153])).
% 6.88/2.40  tff(c_165, plain, (![A_6]: (k1_xboole_0!=A_6 | k6_partfun1(A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_159])).
% 6.88/2.40  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_334, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_165, c_60])).
% 6.88/2.40  tff(c_358, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_334])).
% 6.88/2.40  tff(c_76, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_74, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_280, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.88/2.40  tff(c_298, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_280])).
% 6.88/2.40  tff(c_307, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.88/2.40  tff(c_323, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_307])).
% 6.88/2.40  tff(c_409, plain, (![B_75, A_76]: (k2_relat_1(B_75)=A_76 | ~v2_funct_2(B_75, A_76) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.88/2.40  tff(c_418, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_323, c_409])).
% 6.88/2.40  tff(c_430, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_418])).
% 6.88/2.40  tff(c_434, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_430])).
% 6.88/2.40  tff(c_72, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_1012, plain, (![C_124, B_125, A_126]: (v2_funct_2(C_124, B_125) | ~v3_funct_2(C_124, A_126, B_125) | ~v1_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.88/2.40  tff(c_1024, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1012])).
% 6.88/2.40  tff(c_1033, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1024])).
% 6.88/2.40  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_1033])).
% 6.88/2.40  tff(c_1036, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_430])).
% 6.88/2.40  tff(c_1394, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.88/2.40  tff(c_1406, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1394])).
% 6.88/2.40  tff(c_1414, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1406])).
% 6.88/2.40  tff(c_1446, plain, (![C_161, A_162, B_163]: (v2_funct_1(C_161) | ~v3_funct_2(C_161, A_162, B_163) | ~v1_funct_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.88/2.40  tff(c_1458, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1446])).
% 6.88/2.40  tff(c_1468, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_1458])).
% 6.88/2.40  tff(c_2094, plain, (![C_204, D_205, B_206, A_207]: (k2_funct_1(C_204)=D_205 | k1_xboole_0=B_206 | k1_xboole_0=A_207 | ~v2_funct_1(C_204) | ~r2_relset_1(A_207, A_207, k1_partfun1(A_207, B_206, B_206, A_207, C_204, D_205), k6_partfun1(A_207)) | k2_relset_1(A_207, B_206, C_204)!=B_206 | ~m1_subset_1(D_205, k1_zfmisc_1(k2_zfmisc_1(B_206, A_207))) | ~v1_funct_2(D_205, B_206, A_207) | ~v1_funct_1(D_205) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))) | ~v1_funct_2(C_204, A_207, B_206) | ~v1_funct_1(C_204))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.88/2.40  tff(c_2100, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_2094])).
% 6.88/2.40  tff(c_2106, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_62, c_1414, c_1468, c_2100])).
% 6.88/2.40  tff(c_2107, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_358, c_2106])).
% 6.88/2.40  tff(c_1716, plain, (![A_182, B_183]: (k2_funct_2(A_182, B_183)=k2_funct_1(B_183) | ~m1_subset_1(B_183, k1_zfmisc_1(k2_zfmisc_1(A_182, A_182))) | ~v3_funct_2(B_183, A_182, A_182) | ~v1_funct_2(B_183, A_182, A_182) | ~v1_funct_1(B_183))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.88/2.40  tff(c_1728, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1716])).
% 6.88/2.40  tff(c_1736, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1728])).
% 6.88/2.40  tff(c_58, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_1741, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1736, c_58])).
% 6.88/2.40  tff(c_2108, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2107, c_1741])).
% 6.88/2.40  tff(c_2112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1392, c_2108])).
% 6.88/2.40  tff(c_2114, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_334])).
% 6.88/2.40  tff(c_6, plain, (![A_4]: (k2_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.88/2.40  tff(c_331, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_298, c_6])).
% 6.88/2.40  tff(c_340, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_331])).
% 6.88/2.40  tff(c_2115, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2114, c_340])).
% 6.88/2.40  tff(c_2684, plain, (![B_244, A_245]: (k2_relat_1(B_244)=A_245 | ~v2_funct_2(B_244, A_245) | ~v5_relat_1(B_244, A_245) | ~v1_relat_1(B_244))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.88/2.40  tff(c_2693, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_323, c_2684])).
% 6.88/2.40  tff(c_2702, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_2693])).
% 6.88/2.40  tff(c_2703, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2115, c_2702])).
% 6.88/2.40  tff(c_2938, plain, (![C_265, B_266, A_267]: (v2_funct_2(C_265, B_266) | ~v3_funct_2(C_265, A_267, B_266) | ~v1_funct_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.88/2.40  tff(c_2947, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_2938])).
% 6.88/2.40  tff(c_2955, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_2947])).
% 6.88/2.40  tff(c_2957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2703, c_2955])).
% 6.88/2.40  tff(c_2958, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_331])).
% 6.88/2.40  tff(c_99, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.88/2.40  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.88/2.40  tff(c_105, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_14])).
% 6.88/2.40  tff(c_10, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.88/2.40  tff(c_133, plain, (![A_48]: (k1_relat_1(k6_partfun1(A_48))=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 6.88/2.40  tff(c_142, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_133])).
% 6.88/2.40  tff(c_2969, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_2958, c_142])).
% 6.88/2.40  tff(c_8, plain, (![A_4]: (k1_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.88/2.40  tff(c_330, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_298, c_8])).
% 6.88/2.40  tff(c_339, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_330])).
% 6.88/2.40  tff(c_2960, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_339])).
% 6.88/2.40  tff(c_3007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2969, c_2960])).
% 6.88/2.40  tff(c_3008, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_330])).
% 6.88/2.40  tff(c_3114, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_2') | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_334])).
% 6.88/2.40  tff(c_3115, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_3114])).
% 6.88/2.40  tff(c_117, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_105, c_80])).
% 6.88/2.40  tff(c_3036, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_117])).
% 6.88/2.40  tff(c_3171, plain, (![B_280, A_281]: (k2_relat_1(B_280)=A_281 | ~v2_funct_2(B_280, A_281) | ~v5_relat_1(B_280, A_281) | ~v1_relat_1(B_280))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.88/2.40  tff(c_3180, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_323, c_3171])).
% 6.88/2.40  tff(c_3192, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_3036, c_3180])).
% 6.88/2.40  tff(c_3193, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3115, c_3192])).
% 6.88/2.40  tff(c_3472, plain, (![C_301, B_302, A_303]: (v2_funct_2(C_301, B_302) | ~v3_funct_2(C_301, A_303, B_302) | ~v1_funct_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.88/2.40  tff(c_3484, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_3472])).
% 6.88/2.40  tff(c_3495, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_3484])).
% 6.88/2.40  tff(c_3497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3193, c_3495])).
% 6.88/2.40  tff(c_3499, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3114])).
% 6.88/2.40  tff(c_3508, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3008])).
% 6.88/2.40  tff(c_191, plain, (![A_52]: (k1_xboole_0!=A_52 | k6_partfun1(A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_159])).
% 6.88/2.40  tff(c_46, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.88/2.40  tff(c_197, plain, (![A_52]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | k1_xboole_0!=A_52)), inference(superposition, [status(thm), theory('equality')], [c_191, c_46])).
% 6.88/2.40  tff(c_4093, plain, (![A_347]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_347, A_347))) | A_347!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_3508, c_197])).
% 6.88/2.40  tff(c_30, plain, (![A_19, B_20, D_22]: (r2_relset_1(A_19, B_20, D_22, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.88/2.40  tff(c_4144, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_4093, c_30])).
% 6.88/2.40  tff(c_3514, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_74])).
% 6.88/2.40  tff(c_3515, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_72])).
% 6.88/2.40  tff(c_3516, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_76])).
% 6.88/2.40  tff(c_3031, plain, (![A_6]: (A_6!='#skF_2' | k6_partfun1(A_6)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_165])).
% 6.88/2.40  tff(c_3908, plain, (![A_6]: (A_6!='#skF_1' | k6_partfun1(A_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3031])).
% 6.88/2.40  tff(c_3511, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_298])).
% 6.88/2.40  tff(c_18, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.88/2.40  tff(c_78, plain, (![A_6]: (v2_funct_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 6.88/2.40  tff(c_124, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_78])).
% 6.88/2.40  tff(c_3037, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_124])).
% 6.88/2.40  tff(c_3507, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3037])).
% 6.88/2.40  tff(c_3503, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3036])).
% 6.88/2.40  tff(c_3909, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3031])).
% 6.88/2.40  tff(c_3035, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_142])).
% 6.88/2.40  tff(c_3504, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3035])).
% 6.88/2.40  tff(c_122, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_105, c_79])).
% 6.88/2.40  tff(c_166, plain, (![A_51]: (k8_relat_1(k2_relat_1(A_51), A_51)=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.88/2.40  tff(c_175, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_166])).
% 6.88/2.40  tff(c_182, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_175])).
% 6.88/2.40  tff(c_3032, plain, (k8_relat_1('#skF_2', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_3008, c_182])).
% 6.88/2.40  tff(c_3635, plain, (k8_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3499, c_3032])).
% 6.88/2.40  tff(c_3039, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_14])).
% 6.88/2.40  tff(c_3505, plain, (k6_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3039])).
% 6.88/2.40  tff(c_3538, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_50, c_3505])).
% 6.88/2.40  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.88/2.40  tff(c_82, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_partfun1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2])).
% 6.88/2.40  tff(c_4157, plain, (![B_352]: (k8_relat_1('#skF_1', B_352)=k5_relat_1(B_352, '#skF_1') | ~v1_relat_1(B_352))), inference(superposition, [status(thm), theory('equality')], [c_3538, c_82])).
% 6.88/2.40  tff(c_4160, plain, (k8_relat_1('#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3511, c_4157])).
% 6.88/2.40  tff(c_4165, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_4160])).
% 6.88/2.40  tff(c_3911, plain, (![A_332]: (A_332!='#skF_1' | k6_partfun1(A_332)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3031])).
% 6.88/2.40  tff(c_4237, plain, (![A_359, B_360]: (k8_relat_1(A_359, B_360)=k5_relat_1(B_360, '#skF_1') | ~v1_relat_1(B_360) | A_359!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3911, c_82])).
% 6.88/2.40  tff(c_4239, plain, (![A_359]: (k8_relat_1(A_359, '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | A_359!='#skF_1')), inference(resolution, [status(thm)], [c_3511, c_4237])).
% 6.88/2.40  tff(c_4243, plain, (![A_359]: (k8_relat_1(A_359, '#skF_1')='#skF_1' | A_359!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_4239])).
% 6.88/2.40  tff(c_81, plain, (![A_5]: (k1_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 6.88/2.40  tff(c_20, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.88/2.40  tff(c_4549, plain, (![A_372, B_373]: (k2_funct_1(A_372)=B_373 | k6_partfun1(k1_relat_1(A_372))!=k5_relat_1(A_372, B_373) | k2_relat_1(A_372)!=k1_relat_1(B_373) | ~v2_funct_1(A_372) | ~v1_funct_1(B_373) | ~v1_relat_1(B_373) | ~v1_funct_1(A_372) | ~v1_relat_1(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 6.88/2.40  tff(c_4559, plain, (![A_1, B_2]: (k6_partfun1(A_1)=k2_funct_1(B_2) | k8_relat_1(A_1, B_2)!=k6_partfun1(k1_relat_1(B_2)) | k2_relat_1(B_2)!=k1_relat_1(k6_partfun1(A_1)) | ~v2_funct_1(B_2) | ~v1_funct_1(k6_partfun1(A_1)) | ~v1_relat_1(k6_partfun1(A_1)) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4549])).
% 6.88/2.40  tff(c_5720, plain, (![A_433, B_434]: (k6_partfun1(A_433)=k2_funct_1(B_434) | k8_relat_1(A_433, B_434)!=k6_partfun1(k1_relat_1(B_434)) | k2_relat_1(B_434)!=A_433 | ~v2_funct_1(B_434) | ~v1_funct_1(k6_partfun1(A_433)) | ~v1_funct_1(B_434) | ~v1_relat_1(B_434))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_81, c_4559])).
% 6.88/2.40  tff(c_5747, plain, (![A_359]: (k6_partfun1(A_359)=k2_funct_1('#skF_1') | k6_partfun1(k1_relat_1('#skF_1'))!='#skF_1' | k2_relat_1('#skF_1')!=A_359 | ~v2_funct_1('#skF_1') | ~v1_funct_1(k6_partfun1(A_359)) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | A_359!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4243, c_5720])).
% 6.88/2.40  tff(c_5784, plain, (![A_435]: (k6_partfun1(A_435)=k2_funct_1('#skF_1') | ~v1_funct_1(k6_partfun1(A_435)) | A_435!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3511, c_3516, c_3507, c_3503, c_3909, c_3504, c_5747])).
% 6.88/2.40  tff(c_5802, plain, (![A_6]: (k6_partfun1(A_6)=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | A_6!='#skF_1' | A_6!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3908, c_5784])).
% 6.88/2.40  tff(c_5806, plain, (![A_436]: (k6_partfun1(A_436)=k2_funct_1('#skF_1') | A_436!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3516, c_5802])).
% 6.88/2.40  tff(c_6018, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5806, c_80])).
% 6.88/2.40  tff(c_178, plain, (![A_5]: (k8_relat_1(A_5, k6_partfun1(A_5))=k6_partfun1(A_5) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_166])).
% 6.88/2.40  tff(c_184, plain, (![A_5]: (k8_relat_1(A_5, k6_partfun1(A_5))=k6_partfun1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_178])).
% 6.88/2.40  tff(c_4561, plain, (![A_5, B_373]: (k2_funct_1(k6_partfun1(A_5))=B_373 | k5_relat_1(k6_partfun1(A_5), B_373)!=k6_partfun1(A_5) | k2_relat_1(k6_partfun1(A_5))!=k1_relat_1(B_373) | ~v2_funct_1(k6_partfun1(A_5)) | ~v1_funct_1(B_373) | ~v1_relat_1(B_373) | ~v1_funct_1(k6_partfun1(A_5)) | ~v1_relat_1(k6_partfun1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_81, c_4549])).
% 6.88/2.40  tff(c_5460, plain, (![A_427, B_428]: (k2_funct_1(k6_partfun1(A_427))=B_428 | k5_relat_1(k6_partfun1(A_427), B_428)!=k6_partfun1(A_427) | k1_relat_1(B_428)!=A_427 | ~v1_funct_1(B_428) | ~v1_relat_1(B_428) | ~v1_funct_1(k6_partfun1(A_427)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_80, c_4561])).
% 6.88/2.40  tff(c_5481, plain, (![A_1, A_427]: (k6_partfun1(A_1)=k2_funct_1(k6_partfun1(A_427)) | k8_relat_1(A_1, k6_partfun1(A_427))!=k6_partfun1(A_427) | k1_relat_1(k6_partfun1(A_1))!=A_427 | ~v1_funct_1(k6_partfun1(A_1)) | ~v1_relat_1(k6_partfun1(A_1)) | ~v1_funct_1(k6_partfun1(A_427)) | ~v1_relat_1(k6_partfun1(A_427)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_5460])).
% 6.88/2.40  tff(c_5495, plain, (![A_429]: (k2_funct_1(k6_partfun1(A_429))=k6_partfun1(A_429) | ~v1_funct_1(k6_partfun1(A_429)))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_79, c_79, c_81, c_5481])).
% 6.88/2.40  tff(c_5510, plain, (![A_6]: (k2_funct_1(k6_partfun1(A_6))=k6_partfun1(A_6) | ~v1_funct_1('#skF_1') | A_6!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3908, c_5495])).
% 6.88/2.40  tff(c_5514, plain, (![A_430]: (k2_funct_1(k6_partfun1(A_430))=k6_partfun1(A_430) | A_430!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3516, c_5510])).
% 6.88/2.40  tff(c_5539, plain, (![A_431]: (k6_partfun1(A_431)=k2_funct_1('#skF_1') | A_431!='#skF_1' | A_431!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3908, c_5514])).
% 6.88/2.40  tff(c_5663, plain, (![A_431]: (v1_relat_1(k2_funct_1('#skF_1')) | A_431!='#skF_1' | A_431!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5539, c_79])).
% 6.88/2.40  tff(c_5688, plain, (![A_431]: (A_431!='#skF_1' | A_431!='#skF_1')), inference(splitLeft, [status(thm)], [c_5663])).
% 6.88/2.40  tff(c_5694, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_5688])).
% 6.88/2.40  tff(c_5695, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_5663])).
% 6.88/2.40  tff(c_3033, plain, (![A_4]: (k2_relat_1(A_4)!='#skF_2' | A_4='#skF_2' | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3008, c_3008, c_6])).
% 6.88/2.40  tff(c_4006, plain, (![A_4]: (k2_relat_1(A_4)!='#skF_1' | A_4='#skF_1' | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_3499, c_3033])).
% 6.88/2.40  tff(c_5710, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_5695, c_4006])).
% 6.88/2.40  tff(c_5782, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_5710])).
% 6.88/2.40  tff(c_6021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6018, c_5782])).
% 6.88/2.40  tff(c_6022, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_5710])).
% 6.88/2.40  tff(c_4090, plain, (![A_52]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | A_52!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_3508, c_197])).
% 6.88/2.40  tff(c_4329, plain, (![A_365, B_366]: (k2_funct_2(A_365, B_366)=k2_funct_1(B_366) | ~m1_subset_1(B_366, k1_zfmisc_1(k2_zfmisc_1(A_365, A_365))) | ~v3_funct_2(B_366, A_365, A_365) | ~v1_funct_2(B_366, A_365, A_365) | ~v1_funct_1(B_366))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.88/2.40  tff(c_4332, plain, (![A_52]: (k2_funct_2(A_52, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_52, A_52) | ~v1_funct_2('#skF_1', A_52, A_52) | ~v1_funct_1('#skF_1') | A_52!='#skF_1')), inference(resolution, [status(thm)], [c_4090, c_4329])).
% 6.88/2.40  tff(c_4338, plain, (![A_52]: (k2_funct_2(A_52, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_52, A_52) | ~v1_funct_2('#skF_1', A_52, A_52) | A_52!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3516, c_4332])).
% 6.88/2.40  tff(c_6459, plain, (![A_463]: (k2_funct_2(A_463, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_463, A_463) | ~v1_funct_2('#skF_1', A_463, A_463) | A_463!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6022, c_4338])).
% 6.88/2.40  tff(c_6462, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3515, c_6459])).
% 6.88/2.40  tff(c_6465, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3514, c_6462])).
% 6.88/2.40  tff(c_297, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_280])).
% 6.88/2.40  tff(c_306, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_297, c_6])).
% 6.88/2.40  tff(c_3724, plain, (k2_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_3508, c_306])).
% 6.88/2.40  tff(c_3725, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3724])).
% 6.88/2.40  tff(c_322, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_307])).
% 6.88/2.40  tff(c_3596, plain, (![B_305, A_306]: (k2_relat_1(B_305)=A_306 | ~v2_funct_2(B_305, A_306) | ~v5_relat_1(B_305, A_306) | ~v1_relat_1(B_305))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.88/2.40  tff(c_3605, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_322, c_3596])).
% 6.88/2.40  tff(c_3614, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_3605])).
% 6.88/2.40  tff(c_3796, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3725, c_3614])).
% 6.88/2.40  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.88/2.40  tff(c_3799, plain, (![C_324, B_325, A_326]: (v2_funct_2(C_324, B_325) | ~v3_funct_2(C_324, A_326, B_325) | ~v1_funct_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.88/2.40  tff(c_3808, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_3799])).
% 6.88/2.40  tff(c_3816, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_3808])).
% 6.88/2.40  tff(c_3818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3796, c_3816])).
% 6.88/2.40  tff(c_3819, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_3724])).
% 6.88/2.40  tff(c_305, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_297, c_8])).
% 6.88/2.40  tff(c_3644, plain, (k1_relat_1('#skF_3')!='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_3508, c_305])).
% 6.88/2.40  tff(c_3645, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3644])).
% 6.88/2.40  tff(c_3821, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3819, c_3645])).
% 6.88/2.40  tff(c_3832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3504, c_3821])).
% 6.88/2.40  tff(c_3833, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_3644])).
% 6.88/2.40  tff(c_3512, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_58])).
% 6.88/2.40  tff(c_3998, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3833, c_3512])).
% 6.88/2.40  tff(c_6466, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6465, c_3998])).
% 6.88/2.40  tff(c_6469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4144, c_6466])).
% 6.88/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.40  
% 6.88/2.40  Inference rules
% 6.88/2.40  ----------------------
% 6.88/2.40  #Ref     : 14
% 6.88/2.40  #Sup     : 1505
% 6.88/2.40  #Fact    : 0
% 6.88/2.40  #Define  : 0
% 6.88/2.40  #Split   : 28
% 6.88/2.40  #Chain   : 0
% 6.88/2.40  #Close   : 0
% 6.88/2.40  
% 6.88/2.40  Ordering : KBO
% 6.88/2.40  
% 6.88/2.40  Simplification rules
% 6.88/2.40  ----------------------
% 6.88/2.40  #Subsume      : 372
% 6.88/2.40  #Demod        : 1214
% 6.88/2.40  #Tautology    : 688
% 6.88/2.40  #SimpNegUnit  : 14
% 6.88/2.40  #BackRed      : 114
% 6.88/2.40  
% 6.88/2.40  #Partial instantiations: 0
% 6.88/2.40  #Strategies tried      : 1
% 6.88/2.40  
% 6.88/2.40  Timing (in seconds)
% 6.88/2.40  ----------------------
% 6.88/2.40  Preprocessing        : 0.36
% 6.88/2.40  Parsing              : 0.20
% 6.88/2.40  CNF conversion       : 0.02
% 6.88/2.40  Main loop            : 1.17
% 6.88/2.41  Inferencing          : 0.39
% 6.88/2.41  Reduction            : 0.44
% 6.88/2.41  Demodulation         : 0.31
% 6.88/2.41  BG Simplification    : 0.05
% 6.88/2.41  Subsumption          : 0.21
% 6.88/2.41  Abstraction          : 0.05
% 6.88/2.41  MUC search           : 0.00
% 6.88/2.41  Cooper               : 0.00
% 6.88/2.41  Total                : 1.61
% 6.88/2.41  Index Insertion      : 0.00
% 6.88/2.41  Index Deletion       : 0.00
% 6.88/2.41  Index Matching       : 0.00
% 6.88/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
