%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:55 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :  195 (1958 expanded)
%              Number of leaves         :   45 ( 652 expanded)
%              Depth                    :   15
%              Number of atoms          :  352 (5697 expanded)
%              Number of equality atoms :  115 (1350 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_186,negated_conjecture,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_164,axiom,(
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

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_179,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_196,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_179])).

tff(c_270,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_relset_1(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_281,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_270])).

tff(c_240,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_255,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_240])).

tff(c_283,plain,(
    ! [B_65,A_66] :
      ( k2_relat_1(B_65) = A_66
      | ~ v2_funct_2(B_65,A_66)
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_295,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_283])).

tff(c_307,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_295])).

tff(c_308,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_391,plain,(
    ! [C_76,B_77,A_78] :
      ( v2_funct_2(C_76,B_77)
      | ~ v3_funct_2(C_76,A_78,B_77)
      | ~ v1_funct_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_400,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_391])).

tff(c_409,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_400])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_409])).

tff(c_412,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_6,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_205,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_196,c_6])).

tff(c_239,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_414,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_239])).

tff(c_74,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_72,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_197,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_179])).

tff(c_256,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_240])).

tff(c_292,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_256,c_283])).

tff(c_304,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_292])).

tff(c_465,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_70,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_511,plain,(
    ! [C_87,B_88,A_89] :
      ( v2_funct_2(C_87,B_88)
      | ~ v3_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_523,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_511])).

tff(c_532,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_523])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_532])).

tff(c_535,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_429,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_447,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_429])).

tff(c_537,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_447])).

tff(c_562,plain,(
    ! [C_90,A_91,B_92] :
      ( v2_funct_1(C_90)
      | ~ v3_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_574,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_562])).

tff(c_584,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_574])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_820,plain,(
    ! [C_128,D_129,B_130,A_131] :
      ( k2_funct_1(C_128) = D_129
      | k1_xboole_0 = B_130
      | k1_xboole_0 = A_131
      | ~ v2_funct_1(C_128)
      | ~ r2_relset_1(A_131,A_131,k1_partfun1(A_131,B_130,B_130,A_131,C_128,D_129),k6_partfun1(A_131))
      | k2_relset_1(A_131,B_130,C_128) != B_130
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(B_130,A_131)))
      | ~ v1_funct_2(D_129,B_130,A_131)
      | ~ v1_funct_1(D_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130)))
      | ~ v1_funct_2(C_128,A_131,B_130)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_823,plain,
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
    inference(resolution,[status(thm)],[c_58,c_820])).

tff(c_829,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_60,c_537,c_584,c_823])).

tff(c_830,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_829])).

tff(c_670,plain,(
    ! [A_104,B_105] :
      ( k2_funct_2(A_104,B_105) = k2_funct_1(B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_zfmisc_1(A_104,A_104)))
      | ~ v3_funct_2(B_105,A_104,A_104)
      | ~ v1_funct_2(B_105,A_104,A_104)
      | ~ v1_funct_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_682,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_670])).

tff(c_690,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_682])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_712,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_56])).

tff(c_834,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_712])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_834])).

tff(c_839,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_857,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_839,c_4])).

tff(c_8,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_204,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_196,c_8])).

tff(c_214,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_844,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_214])).

tff(c_922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_844])).

tff(c_923,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_937,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_923,c_2])).

tff(c_966,plain,(
    ! [C_135,B_136,A_137] :
      ( v5_relat_1(C_135,B_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_977,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_966])).

tff(c_1088,plain,(
    ! [B_150,A_151] :
      ( k2_relat_1(B_150) = A_151
      | ~ v2_funct_2(B_150,A_151)
      | ~ v5_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1100,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_977,c_1088])).

tff(c_1112,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_937,c_1100])).

tff(c_1113,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1208,plain,(
    ! [C_161,B_162,A_163] :
      ( v2_funct_2(C_161,B_162)
      | ~ v3_funct_2(C_161,A_163,B_162)
      | ~ v1_funct_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1217,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1208])).

tff(c_1227,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1217])).

tff(c_1229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1113,c_1227])).

tff(c_1230,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_213,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_197,c_6])).

tff(c_925,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_1003,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_925])).

tff(c_1243,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1230,c_1003])).

tff(c_1362,plain,(
    ! [C_170,B_171,A_172] :
      ( v2_funct_2(C_170,B_171)
      | ~ v3_funct_2(C_170,A_172,B_171)
      | ~ v1_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1368,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1362])).

tff(c_1372,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_1368])).

tff(c_978,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_966])).

tff(c_1097,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_978,c_1088])).

tff(c_1109,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1097])).

tff(c_1386,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_1109])).

tff(c_1387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1243,c_1386])).

tff(c_1388,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_1425,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_1388])).

tff(c_1389,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_1459,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_923,c_1389])).

tff(c_1390,plain,(
    ! [C_173,B_174,A_175] :
      ( v5_relat_1(C_173,B_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_175,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1405,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1390])).

tff(c_1539,plain,(
    ! [B_182,A_183] :
      ( k2_relat_1(B_182) = A_183
      | ~ v2_funct_2(B_182,A_183)
      | ~ v5_relat_1(B_182,A_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1548,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1405,c_1539])).

tff(c_1557,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_1459,c_1548])).

tff(c_1558,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1557])).

tff(c_1674,plain,(
    ! [C_200,B_201,A_202] :
      ( v2_funct_2(C_200,B_201)
      | ~ v3_funct_2(C_200,A_202,B_201)
      | ~ v1_funct_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1683,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1674])).

tff(c_1690,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1683])).

tff(c_1692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1558,c_1690])).

tff(c_1693,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1557])).

tff(c_1695,plain,(
    ! [A_203,B_204,D_205] :
      ( r2_relset_1(A_203,B_204,D_205,D_205)
      | ~ m1_subset_1(D_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1704,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1695])).

tff(c_1820,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_1704])).

tff(c_1726,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_66])).

tff(c_1716,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_1459])).

tff(c_94,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_12])).

tff(c_48,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_3] : v1_relat_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_114,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_77])).

tff(c_10,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k6_relat_1(k2_relat_1(A_2))) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_149,plain,(
    ! [A_47] :
      ( k5_relat_1(A_47,k6_partfun1(k2_relat_1(A_47))) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_158,plain,
    ( k5_relat_1(k1_xboole_0,k6_partfun1(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_162,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_100,c_158])).

tff(c_1409,plain,(
    k5_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_923,c_923,c_162])).

tff(c_1707,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_1693,c_1409])).

tff(c_1722,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_196])).

tff(c_16,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_116,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_76])).

tff(c_1414,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_116])).

tff(c_1719,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1414])).

tff(c_924,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_1469,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_924])).

tff(c_1714,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_1469])).

tff(c_1416,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_923,c_100])).

tff(c_1717,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_1416])).

tff(c_18,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_relat_1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1976,plain,(
    ! [A_229,B_230] :
      ( k2_funct_1(A_229) = B_230
      | k6_partfun1(k2_relat_1(A_229)) != k5_relat_1(B_230,A_229)
      | k2_relat_1(B_230) != k1_relat_1(A_229)
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_1978,plain,(
    ! [B_230] :
      ( k2_funct_1('#skF_1') = B_230
      | k5_relat_1(B_230,'#skF_1') != k6_partfun1('#skF_1')
      | k2_relat_1(B_230) != k1_relat_1('#skF_1')
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1716,c_1976])).

tff(c_1990,plain,(
    ! [B_231] :
      ( k2_funct_1('#skF_1') = B_231
      | k5_relat_1(B_231,'#skF_1') != '#skF_1'
      | k2_relat_1(B_231) != '#skF_1'
      | ~ v1_funct_1(B_231)
      | ~ v1_relat_1(B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1722,c_1726,c_1719,c_1714,c_1717,c_1978])).

tff(c_1993,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1722,c_1990])).

tff(c_1999,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1716,c_1707,c_1993])).

tff(c_1724,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_64])).

tff(c_1725,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_62])).

tff(c_1723,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_60])).

tff(c_1965,plain,(
    ! [A_227,B_228] :
      ( k2_funct_2(A_227,B_228) = k2_funct_1(B_228)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k2_zfmisc_1(A_227,A_227)))
      | ~ v3_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_2(B_228,A_227,A_227)
      | ~ v1_funct_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1968,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1723,c_1965])).

tff(c_1974,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1724,c_1725,c_1968])).

tff(c_1428,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_56])).

tff(c_1711,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_1693,c_1428])).

tff(c_1985,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1974,c_1711])).

tff(c_2002,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_1985])).

tff(c_2006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_2002])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.68  
% 3.94/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.68  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.94/1.68  
% 3.94/1.68  %Foreground sorts:
% 3.94/1.68  
% 3.94/1.68  
% 3.94/1.68  %Background operators:
% 3.94/1.68  
% 3.94/1.68  
% 3.94/1.68  %Foreground operators:
% 3.94/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.94/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.94/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.94/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.94/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.94/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.94/1.68  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.94/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.94/1.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.94/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.94/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.94/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.68  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.94/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.94/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.94/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.94/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.94/1.68  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.94/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.68  
% 4.29/1.71  tff(f_186, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 4.29/1.71  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.29/1.71  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.29/1.71  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.29/1.71  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.29/1.71  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.29/1.71  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.29/1.71  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.29/1.71  tff(f_164, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.29/1.71  tff(f_118, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.29/1.71  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.29/1.71  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.29/1.71  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.29/1.71  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.29/1.71  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 4.29/1.71  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 4.29/1.71  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_179, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.29/1.71  tff(c_196, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_179])).
% 4.29/1.71  tff(c_270, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.29/1.71  tff(c_281, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_270])).
% 4.29/1.71  tff(c_240, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.29/1.71  tff(c_255, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_240])).
% 4.29/1.71  tff(c_283, plain, (![B_65, A_66]: (k2_relat_1(B_65)=A_66 | ~v2_funct_2(B_65, A_66) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.29/1.71  tff(c_295, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_283])).
% 4.29/1.71  tff(c_307, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_295])).
% 4.29/1.71  tff(c_308, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_307])).
% 4.29/1.71  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_391, plain, (![C_76, B_77, A_78]: (v2_funct_2(C_76, B_77) | ~v3_funct_2(C_76, A_78, B_77) | ~v1_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.29/1.71  tff(c_400, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_391])).
% 4.29/1.71  tff(c_409, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_400])).
% 4.29/1.71  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_409])).
% 4.29/1.71  tff(c_412, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_307])).
% 4.29/1.71  tff(c_6, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.29/1.71  tff(c_205, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_196, c_6])).
% 4.29/1.71  tff(c_239, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_205])).
% 4.29/1.71  tff(c_414, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_239])).
% 4.29/1.71  tff(c_74, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_72, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_197, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_179])).
% 4.29/1.71  tff(c_256, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_240])).
% 4.29/1.71  tff(c_292, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_256, c_283])).
% 4.29/1.71  tff(c_304, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_292])).
% 4.29/1.71  tff(c_465, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_304])).
% 4.29/1.71  tff(c_70, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_511, plain, (![C_87, B_88, A_89]: (v2_funct_2(C_87, B_88) | ~v3_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.29/1.71  tff(c_523, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_511])).
% 4.29/1.71  tff(c_532, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_523])).
% 4.29/1.71  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_465, c_532])).
% 4.29/1.71  tff(c_535, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_304])).
% 4.29/1.71  tff(c_429, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.29/1.71  tff(c_447, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_429])).
% 4.29/1.71  tff(c_537, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_447])).
% 4.29/1.71  tff(c_562, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.29/1.71  tff(c_574, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_562])).
% 4.29/1.71  tff(c_584, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_574])).
% 4.29/1.71  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_820, plain, (![C_128, D_129, B_130, A_131]: (k2_funct_1(C_128)=D_129 | k1_xboole_0=B_130 | k1_xboole_0=A_131 | ~v2_funct_1(C_128) | ~r2_relset_1(A_131, A_131, k1_partfun1(A_131, B_130, B_130, A_131, C_128, D_129), k6_partfun1(A_131)) | k2_relset_1(A_131, B_130, C_128)!=B_130 | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(B_130, A_131))) | ~v1_funct_2(D_129, B_130, A_131) | ~v1_funct_1(D_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))) | ~v1_funct_2(C_128, A_131, B_130) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.29/1.71  tff(c_823, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_820])).
% 4.29/1.71  tff(c_829, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_60, c_537, c_584, c_823])).
% 4.29/1.71  tff(c_830, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_414, c_829])).
% 4.29/1.71  tff(c_670, plain, (![A_104, B_105]: (k2_funct_2(A_104, B_105)=k2_funct_1(B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_zfmisc_1(A_104, A_104))) | ~v3_funct_2(B_105, A_104, A_104) | ~v1_funct_2(B_105, A_104, A_104) | ~v1_funct_1(B_105))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.29/1.71  tff(c_682, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_670])).
% 4.29/1.71  tff(c_690, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_682])).
% 4.29/1.71  tff(c_56, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.29/1.71  tff(c_712, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_56])).
% 4.29/1.71  tff(c_834, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_712])).
% 4.29/1.71  tff(c_838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_834])).
% 4.29/1.71  tff(c_839, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_205])).
% 4.29/1.71  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.29/1.71  tff(c_857, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_839, c_839, c_4])).
% 4.29/1.71  tff(c_8, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.29/1.71  tff(c_204, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_196, c_8])).
% 4.29/1.71  tff(c_214, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_204])).
% 4.29/1.71  tff(c_844, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_839, c_214])).
% 4.29/1.71  tff(c_922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_857, c_844])).
% 4.29/1.71  tff(c_923, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_204])).
% 4.29/1.71  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.29/1.71  tff(c_937, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_923, c_2])).
% 4.29/1.71  tff(c_966, plain, (![C_135, B_136, A_137]: (v5_relat_1(C_135, B_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.29/1.71  tff(c_977, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_966])).
% 4.29/1.71  tff(c_1088, plain, (![B_150, A_151]: (k2_relat_1(B_150)=A_151 | ~v2_funct_2(B_150, A_151) | ~v5_relat_1(B_150, A_151) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.29/1.71  tff(c_1100, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_977, c_1088])).
% 4.29/1.71  tff(c_1112, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_937, c_1100])).
% 4.29/1.71  tff(c_1113, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1112])).
% 4.29/1.71  tff(c_1208, plain, (![C_161, B_162, A_163]: (v2_funct_2(C_161, B_162) | ~v3_funct_2(C_161, A_163, B_162) | ~v1_funct_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.29/1.71  tff(c_1217, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1208])).
% 4.29/1.71  tff(c_1227, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1217])).
% 4.29/1.71  tff(c_1229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1113, c_1227])).
% 4.29/1.71  tff(c_1230, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1112])).
% 4.29/1.71  tff(c_213, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_197, c_6])).
% 4.29/1.71  tff(c_925, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_213])).
% 4.29/1.71  tff(c_1003, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_925])).
% 4.29/1.71  tff(c_1243, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1230, c_1003])).
% 4.29/1.71  tff(c_1362, plain, (![C_170, B_171, A_172]: (v2_funct_2(C_170, B_171) | ~v3_funct_2(C_170, A_172, B_171) | ~v1_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.29/1.71  tff(c_1368, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_1362])).
% 4.29/1.71  tff(c_1372, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_1368])).
% 4.29/1.71  tff(c_978, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_966])).
% 4.29/1.71  tff(c_1097, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_978, c_1088])).
% 4.29/1.71  tff(c_1109, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_1097])).
% 4.29/1.71  tff(c_1386, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_1109])).
% 4.29/1.71  tff(c_1387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1243, c_1386])).
% 4.29/1.71  tff(c_1388, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_213])).
% 4.29/1.71  tff(c_1425, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_1388])).
% 4.29/1.71  tff(c_1389, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_213])).
% 4.29/1.71  tff(c_1459, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_923, c_1389])).
% 4.29/1.71  tff(c_1390, plain, (![C_173, B_174, A_175]: (v5_relat_1(C_173, B_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_175, B_174))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.29/1.71  tff(c_1405, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1390])).
% 4.29/1.71  tff(c_1539, plain, (![B_182, A_183]: (k2_relat_1(B_182)=A_183 | ~v2_funct_2(B_182, A_183) | ~v5_relat_1(B_182, A_183) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.29/1.71  tff(c_1548, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1405, c_1539])).
% 4.29/1.71  tff(c_1557, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_1459, c_1548])).
% 4.29/1.71  tff(c_1558, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1557])).
% 4.29/1.71  tff(c_1674, plain, (![C_200, B_201, A_202]: (v2_funct_2(C_200, B_201) | ~v3_funct_2(C_200, A_202, B_201) | ~v1_funct_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.29/1.71  tff(c_1683, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1674])).
% 4.29/1.71  tff(c_1690, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1683])).
% 4.29/1.71  tff(c_1692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1558, c_1690])).
% 4.29/1.71  tff(c_1693, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1557])).
% 4.29/1.71  tff(c_1695, plain, (![A_203, B_204, D_205]: (r2_relset_1(A_203, B_204, D_205, D_205) | ~m1_subset_1(D_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.29/1.71  tff(c_1704, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1695])).
% 4.29/1.71  tff(c_1820, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_1704])).
% 4.29/1.71  tff(c_1726, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_66])).
% 4.29/1.71  tff(c_1716, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_1459])).
% 4.29/1.71  tff(c_94, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.71  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.71  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_12])).
% 4.29/1.71  tff(c_48, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.29/1.71  tff(c_14, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.29/1.71  tff(c_77, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 4.29/1.71  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_77])).
% 4.29/1.71  tff(c_10, plain, (![A_2]: (k5_relat_1(A_2, k6_relat_1(k2_relat_1(A_2)))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.29/1.71  tff(c_149, plain, (![A_47]: (k5_relat_1(A_47, k6_partfun1(k2_relat_1(A_47)))=A_47 | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 4.29/1.71  tff(c_158, plain, (k5_relat_1(k1_xboole_0, k6_partfun1(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 4.29/1.71  tff(c_162, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_100, c_158])).
% 4.29/1.71  tff(c_1409, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_923, c_923, c_162])).
% 4.29/1.71  tff(c_1707, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_1693, c_1409])).
% 4.29/1.71  tff(c_1722, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_196])).
% 4.29/1.71  tff(c_16, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.29/1.71  tff(c_76, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 4.29/1.71  tff(c_116, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_76])).
% 4.29/1.71  tff(c_1414, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_923, c_116])).
% 4.29/1.71  tff(c_1719, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1414])).
% 4.29/1.71  tff(c_924, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_204])).
% 4.29/1.71  tff(c_1469, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_924])).
% 4.29/1.71  tff(c_1714, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_1469])).
% 4.29/1.71  tff(c_1416, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_923, c_923, c_100])).
% 4.29/1.71  tff(c_1717, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_1416])).
% 4.29/1.71  tff(c_18, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.29/1.71  tff(c_1976, plain, (![A_229, B_230]: (k2_funct_1(A_229)=B_230 | k6_partfun1(k2_relat_1(A_229))!=k5_relat_1(B_230, A_229) | k2_relat_1(B_230)!=k1_relat_1(A_229) | ~v2_funct_1(A_229) | ~v1_funct_1(B_230) | ~v1_relat_1(B_230) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 4.29/1.71  tff(c_1978, plain, (![B_230]: (k2_funct_1('#skF_1')=B_230 | k5_relat_1(B_230, '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1(B_230)!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_230) | ~v1_relat_1(B_230) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1716, c_1976])).
% 4.29/1.71  tff(c_1990, plain, (![B_231]: (k2_funct_1('#skF_1')=B_231 | k5_relat_1(B_231, '#skF_1')!='#skF_1' | k2_relat_1(B_231)!='#skF_1' | ~v1_funct_1(B_231) | ~v1_relat_1(B_231))), inference(demodulation, [status(thm), theory('equality')], [c_1722, c_1726, c_1719, c_1714, c_1717, c_1978])).
% 4.29/1.71  tff(c_1993, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k2_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1722, c_1990])).
% 4.29/1.71  tff(c_1999, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1716, c_1707, c_1993])).
% 4.29/1.71  tff(c_1724, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_64])).
% 4.29/1.71  tff(c_1725, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_62])).
% 4.29/1.71  tff(c_1723, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_60])).
% 4.29/1.71  tff(c_1965, plain, (![A_227, B_228]: (k2_funct_2(A_227, B_228)=k2_funct_1(B_228) | ~m1_subset_1(B_228, k1_zfmisc_1(k2_zfmisc_1(A_227, A_227))) | ~v3_funct_2(B_228, A_227, A_227) | ~v1_funct_2(B_228, A_227, A_227) | ~v1_funct_1(B_228))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.29/1.71  tff(c_1968, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1723, c_1965])).
% 4.29/1.71  tff(c_1974, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1724, c_1725, c_1968])).
% 4.29/1.71  tff(c_1428, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_56])).
% 4.29/1.71  tff(c_1711, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1693, c_1693, c_1428])).
% 4.29/1.71  tff(c_1985, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1974, c_1711])).
% 4.29/1.71  tff(c_2002, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_1985])).
% 4.29/1.71  tff(c_2006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1820, c_2002])).
% 4.29/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.71  
% 4.29/1.71  Inference rules
% 4.29/1.71  ----------------------
% 4.29/1.71  #Ref     : 0
% 4.29/1.71  #Sup     : 421
% 4.29/1.71  #Fact    : 0
% 4.29/1.71  #Define  : 0
% 4.29/1.71  #Split   : 19
% 4.29/1.71  #Chain   : 0
% 4.29/1.71  #Close   : 0
% 4.29/1.71  
% 4.29/1.71  Ordering : KBO
% 4.29/1.71  
% 4.29/1.71  Simplification rules
% 4.29/1.71  ----------------------
% 4.29/1.71  #Subsume      : 20
% 4.29/1.71  #Demod        : 639
% 4.29/1.71  #Tautology    : 292
% 4.29/1.71  #SimpNegUnit  : 6
% 4.29/1.71  #BackRed      : 111
% 4.29/1.71  
% 4.29/1.71  #Partial instantiations: 0
% 4.29/1.71  #Strategies tried      : 1
% 4.29/1.71  
% 4.29/1.71  Timing (in seconds)
% 4.29/1.71  ----------------------
% 4.29/1.71  Preprocessing        : 0.35
% 4.29/1.71  Parsing              : 0.19
% 4.29/1.71  CNF conversion       : 0.02
% 4.29/1.71  Main loop            : 0.58
% 4.29/1.71  Inferencing          : 0.20
% 4.29/1.71  Reduction            : 0.21
% 4.29/1.71  Demodulation         : 0.15
% 4.29/1.71  BG Simplification    : 0.03
% 4.29/1.71  Subsumption          : 0.08
% 4.29/1.71  Abstraction          : 0.04
% 4.29/1.71  MUC search           : 0.00
% 4.29/1.71  Cooper               : 0.00
% 4.29/1.71  Total                : 0.98
% 4.29/1.71  Index Insertion      : 0.00
% 4.29/1.71  Index Deletion       : 0.00
% 4.29/1.71  Index Matching       : 0.00
% 4.29/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
