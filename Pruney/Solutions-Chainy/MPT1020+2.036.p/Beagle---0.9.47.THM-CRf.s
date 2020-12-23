%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:55 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  195 (1939 expanded)
%              Number of leaves         :   45 ( 646 expanded)
%              Depth                    :   15
%              Number of atoms          :  352 (5644 expanded)
%              Number of equality atoms :  115 (1333 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_62,axiom,(
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

tff(c_763,plain,(
    ! [C_124,D_125,B_126,A_127] :
      ( k2_funct_1(C_124) = D_125
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_127
      | ~ v2_funct_1(C_124)
      | ~ r2_relset_1(A_127,A_127,k1_partfun1(A_127,B_126,B_126,A_127,C_124,D_125),k6_partfun1(A_127))
      | k2_relset_1(A_127,B_126,C_124) != B_126
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(B_126,A_127)))
      | ~ v1_funct_2(D_125,B_126,A_127)
      | ~ v1_funct_1(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(C_124,A_127,B_126)
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_766,plain,
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
    inference(resolution,[status(thm)],[c_58,c_763])).

tff(c_772,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_60,c_537,c_584,c_766])).

tff(c_773,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_772])).

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

tff(c_775,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_712])).

tff(c_779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_775])).

tff(c_780,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_815,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_780,c_4])).

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

tff(c_802,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_214])).

tff(c_874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_802])).

tff(c_875,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_889,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_875,c_2])).

tff(c_918,plain,(
    ! [C_132,B_133,A_134] :
      ( v5_relat_1(C_132,B_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_929,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_918])).

tff(c_1040,plain,(
    ! [B_147,A_148] :
      ( k2_relat_1(B_147) = A_148
      | ~ v2_funct_2(B_147,A_148)
      | ~ v5_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1052,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_929,c_1040])).

tff(c_1064,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_889,c_1052])).

tff(c_1065,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_1160,plain,(
    ! [C_158,B_159,A_160] :
      ( v2_funct_2(C_158,B_159)
      | ~ v3_funct_2(C_158,A_160,B_159)
      | ~ v1_funct_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1169,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1160])).

tff(c_1179,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1169])).

tff(c_1181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_1179])).

tff(c_1182,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_213,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_197,c_6])).

tff(c_877,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_955,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_877])).

tff(c_1195,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_955])).

tff(c_1314,plain,(
    ! [C_167,B_168,A_169] :
      ( v2_funct_2(C_167,B_168)
      | ~ v3_funct_2(C_167,A_169,B_168)
      | ~ v1_funct_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1320,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1314])).

tff(c_1324,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_1320])).

tff(c_930,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_918])).

tff(c_1049,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_930,c_1040])).

tff(c_1061,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_1049])).

tff(c_1338,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_1061])).

tff(c_1339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1195,c_1338])).

tff(c_1340,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_1377,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_1340])).

tff(c_1341,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_1411,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_875,c_1341])).

tff(c_1342,plain,(
    ! [C_170,B_171,A_172] :
      ( v5_relat_1(C_170,B_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1357,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1342])).

tff(c_1491,plain,(
    ! [B_179,A_180] :
      ( k2_relat_1(B_179) = A_180
      | ~ v2_funct_2(B_179,A_180)
      | ~ v5_relat_1(B_179,A_180)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1500,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1357,c_1491])).

tff(c_1509,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_1411,c_1500])).

tff(c_1510,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_1626,plain,(
    ! [C_197,B_198,A_199] :
      ( v2_funct_2(C_197,B_198)
      | ~ v3_funct_2(C_197,A_199,B_198)
      | ~ v1_funct_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1635,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1626])).

tff(c_1642,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1635])).

tff(c_1644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_1642])).

tff(c_1645,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_1647,plain,(
    ! [A_200,B_201,D_202] :
      ( r2_relset_1(A_200,B_201,D_202,D_202)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1656,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1647])).

tff(c_1772,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1645,c_1656])).

tff(c_1678,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_66])).

tff(c_876,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_1421,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_876])).

tff(c_1666,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1645,c_1421])).

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

tff(c_1361,plain,(
    k5_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_875,c_875,c_162])).

tff(c_1659,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1645,c_1645,c_1361])).

tff(c_1674,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_196])).

tff(c_16,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_116,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_76])).

tff(c_1366,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_116])).

tff(c_1671,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1366])).

tff(c_1668,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1645,c_1411])).

tff(c_1368,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_875,c_100])).

tff(c_1669,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1645,c_1368])).

tff(c_18,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_relat_1(k1_relat_1(A_4)) != k5_relat_1(A_4,B_6)
      | k2_relat_1(A_4) != k1_relat_1(B_6)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1928,plain,(
    ! [A_226,B_227] :
      ( k2_funct_1(A_226) = B_227
      | k6_partfun1(k1_relat_1(A_226)) != k5_relat_1(A_226,B_227)
      | k2_relat_1(A_226) != k1_relat_1(B_227)
      | ~ v2_funct_1(A_226)
      | ~ v1_funct_1(B_227)
      | ~ v1_relat_1(B_227)
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_1930,plain,(
    ! [B_227] :
      ( k2_funct_1('#skF_1') = B_227
      | k5_relat_1('#skF_1',B_227) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_1') != k1_relat_1(B_227)
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_227)
      | ~ v1_relat_1(B_227)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1666,c_1928])).

tff(c_1942,plain,(
    ! [B_228] :
      ( k2_funct_1('#skF_1') = B_228
      | k5_relat_1('#skF_1',B_228) != '#skF_1'
      | k1_relat_1(B_228) != '#skF_1'
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_1678,c_1671,c_1668,c_1669,c_1930])).

tff(c_1945,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k1_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1674,c_1942])).

tff(c_1951,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1666,c_1659,c_1945])).

tff(c_1676,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_64])).

tff(c_1677,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_62])).

tff(c_1675,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_60])).

tff(c_1917,plain,(
    ! [A_224,B_225] :
      ( k2_funct_2(A_224,B_225) = k2_funct_1(B_225)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(k2_zfmisc_1(A_224,A_224)))
      | ~ v3_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_1(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1920,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1675,c_1917])).

tff(c_1926,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1678,c_1676,c_1677,c_1920])).

tff(c_1380,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_56])).

tff(c_1663,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_1645,c_1380])).

tff(c_1937,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_1663])).

tff(c_1954,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1951,c_1937])).

tff(c_1958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_1954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.70  
% 4.08/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.70  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.08/1.70  
% 4.08/1.70  %Foreground sorts:
% 4.08/1.70  
% 4.08/1.70  
% 4.08/1.70  %Background operators:
% 4.08/1.70  
% 4.08/1.70  
% 4.08/1.70  %Foreground operators:
% 4.08/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.08/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.08/1.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.08/1.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.08/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.08/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.08/1.70  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.08/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.08/1.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.08/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.08/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.08/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.70  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.08/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.08/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.08/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.08/1.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.08/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.08/1.70  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.08/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.08/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.70  
% 4.43/1.73  tff(f_186, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 4.43/1.73  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.43/1.73  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.43/1.73  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.43/1.73  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.43/1.73  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.43/1.73  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.43/1.73  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.43/1.73  tff(f_164, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.43/1.73  tff(f_118, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.43/1.73  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.43/1.73  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.43/1.73  tff(f_41, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.43/1.73  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.43/1.73  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 4.43/1.73  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.43/1.73  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_179, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.43/1.73  tff(c_196, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_179])).
% 4.43/1.73  tff(c_270, plain, (![A_62, B_63, D_64]: (r2_relset_1(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.43/1.73  tff(c_281, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_270])).
% 4.43/1.73  tff(c_240, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.43/1.73  tff(c_255, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_240])).
% 4.43/1.73  tff(c_283, plain, (![B_65, A_66]: (k2_relat_1(B_65)=A_66 | ~v2_funct_2(B_65, A_66) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.43/1.73  tff(c_295, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_283])).
% 4.43/1.73  tff(c_307, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_295])).
% 4.43/1.73  tff(c_308, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_307])).
% 4.43/1.73  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_391, plain, (![C_76, B_77, A_78]: (v2_funct_2(C_76, B_77) | ~v3_funct_2(C_76, A_78, B_77) | ~v1_funct_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.43/1.73  tff(c_400, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_391])).
% 4.43/1.73  tff(c_409, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_400])).
% 4.43/1.73  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_409])).
% 4.43/1.73  tff(c_412, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_307])).
% 4.43/1.73  tff(c_6, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.43/1.73  tff(c_205, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_196, c_6])).
% 4.43/1.73  tff(c_239, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_205])).
% 4.43/1.73  tff(c_414, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_412, c_239])).
% 4.43/1.73  tff(c_74, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_72, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_197, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_179])).
% 4.43/1.73  tff(c_256, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_240])).
% 4.43/1.73  tff(c_292, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_256, c_283])).
% 4.43/1.73  tff(c_304, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_292])).
% 4.43/1.73  tff(c_465, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_304])).
% 4.43/1.73  tff(c_70, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_511, plain, (![C_87, B_88, A_89]: (v2_funct_2(C_87, B_88) | ~v3_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.43/1.73  tff(c_523, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_511])).
% 4.43/1.73  tff(c_532, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_523])).
% 4.43/1.73  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_465, c_532])).
% 4.43/1.73  tff(c_535, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_304])).
% 4.43/1.73  tff(c_429, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.43/1.73  tff(c_447, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_429])).
% 4.43/1.73  tff(c_537, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_447])).
% 4.43/1.73  tff(c_562, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.43/1.73  tff(c_574, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_562])).
% 4.43/1.73  tff(c_584, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_574])).
% 4.43/1.73  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_763, plain, (![C_124, D_125, B_126, A_127]: (k2_funct_1(C_124)=D_125 | k1_xboole_0=B_126 | k1_xboole_0=A_127 | ~v2_funct_1(C_124) | ~r2_relset_1(A_127, A_127, k1_partfun1(A_127, B_126, B_126, A_127, C_124, D_125), k6_partfun1(A_127)) | k2_relset_1(A_127, B_126, C_124)!=B_126 | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(B_126, A_127))) | ~v1_funct_2(D_125, B_126, A_127) | ~v1_funct_1(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(C_124, A_127, B_126) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.43/1.73  tff(c_766, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_763])).
% 4.43/1.73  tff(c_772, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_60, c_537, c_584, c_766])).
% 4.43/1.73  tff(c_773, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_414, c_772])).
% 4.43/1.73  tff(c_670, plain, (![A_104, B_105]: (k2_funct_2(A_104, B_105)=k2_funct_1(B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_zfmisc_1(A_104, A_104))) | ~v3_funct_2(B_105, A_104, A_104) | ~v1_funct_2(B_105, A_104, A_104) | ~v1_funct_1(B_105))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.73  tff(c_682, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_670])).
% 4.43/1.73  tff(c_690, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_682])).
% 4.43/1.73  tff(c_56, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.43/1.73  tff(c_712, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_690, c_56])).
% 4.43/1.73  tff(c_775, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_712])).
% 4.43/1.73  tff(c_779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_775])).
% 4.43/1.73  tff(c_780, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_205])).
% 4.43/1.73  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.43/1.73  tff(c_815, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_780, c_780, c_4])).
% 4.43/1.73  tff(c_8, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.43/1.73  tff(c_204, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_196, c_8])).
% 4.43/1.73  tff(c_214, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_204])).
% 4.43/1.73  tff(c_802, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_780, c_214])).
% 4.43/1.73  tff(c_874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_815, c_802])).
% 4.43/1.73  tff(c_875, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_204])).
% 4.43/1.73  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.43/1.73  tff(c_889, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_875, c_2])).
% 4.43/1.73  tff(c_918, plain, (![C_132, B_133, A_134]: (v5_relat_1(C_132, B_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.43/1.73  tff(c_929, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_918])).
% 4.43/1.73  tff(c_1040, plain, (![B_147, A_148]: (k2_relat_1(B_147)=A_148 | ~v2_funct_2(B_147, A_148) | ~v5_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.43/1.73  tff(c_1052, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_929, c_1040])).
% 4.43/1.73  tff(c_1064, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_889, c_1052])).
% 4.43/1.73  tff(c_1065, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1064])).
% 4.43/1.73  tff(c_1160, plain, (![C_158, B_159, A_160]: (v2_funct_2(C_158, B_159) | ~v3_funct_2(C_158, A_160, B_159) | ~v1_funct_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.43/1.73  tff(c_1169, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1160])).
% 4.43/1.73  tff(c_1179, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1169])).
% 4.43/1.73  tff(c_1181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1065, c_1179])).
% 4.43/1.73  tff(c_1182, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1064])).
% 4.43/1.73  tff(c_213, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_197, c_6])).
% 4.43/1.73  tff(c_877, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_213])).
% 4.43/1.73  tff(c_955, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_877])).
% 4.43/1.73  tff(c_1195, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_955])).
% 4.43/1.73  tff(c_1314, plain, (![C_167, B_168, A_169]: (v2_funct_2(C_167, B_168) | ~v3_funct_2(C_167, A_169, B_168) | ~v1_funct_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.43/1.73  tff(c_1320, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_1314])).
% 4.43/1.73  tff(c_1324, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_1320])).
% 4.43/1.73  tff(c_930, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_918])).
% 4.43/1.73  tff(c_1049, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_930, c_1040])).
% 4.43/1.73  tff(c_1061, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_1049])).
% 4.43/1.73  tff(c_1338, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_1061])).
% 4.43/1.73  tff(c_1339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1195, c_1338])).
% 4.43/1.73  tff(c_1340, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_213])).
% 4.43/1.73  tff(c_1377, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_1340])).
% 4.43/1.73  tff(c_1341, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_213])).
% 4.43/1.73  tff(c_1411, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_875, c_1341])).
% 4.43/1.73  tff(c_1342, plain, (![C_170, B_171, A_172]: (v5_relat_1(C_170, B_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.43/1.73  tff(c_1357, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1342])).
% 4.43/1.73  tff(c_1491, plain, (![B_179, A_180]: (k2_relat_1(B_179)=A_180 | ~v2_funct_2(B_179, A_180) | ~v5_relat_1(B_179, A_180) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.43/1.73  tff(c_1500, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1357, c_1491])).
% 4.43/1.73  tff(c_1509, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_1411, c_1500])).
% 4.43/1.73  tff(c_1510, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1509])).
% 4.43/1.73  tff(c_1626, plain, (![C_197, B_198, A_199]: (v2_funct_2(C_197, B_198) | ~v3_funct_2(C_197, A_199, B_198) | ~v1_funct_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.43/1.73  tff(c_1635, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1626])).
% 4.43/1.73  tff(c_1642, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1635])).
% 4.43/1.73  tff(c_1644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1510, c_1642])).
% 4.43/1.73  tff(c_1645, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1509])).
% 4.43/1.73  tff(c_1647, plain, (![A_200, B_201, D_202]: (r2_relset_1(A_200, B_201, D_202, D_202) | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.43/1.73  tff(c_1656, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1647])).
% 4.43/1.73  tff(c_1772, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1645, c_1656])).
% 4.43/1.73  tff(c_1678, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_66])).
% 4.43/1.73  tff(c_876, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_204])).
% 4.43/1.73  tff(c_1421, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_876])).
% 4.43/1.73  tff(c_1666, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1645, c_1421])).
% 4.43/1.73  tff(c_94, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.43/1.73  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.43/1.73  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_12])).
% 4.43/1.73  tff(c_48, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.43/1.73  tff(c_14, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.43/1.73  tff(c_77, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 4.43/1.73  tff(c_114, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_77])).
% 4.43/1.73  tff(c_10, plain, (![A_2]: (k5_relat_1(A_2, k6_relat_1(k2_relat_1(A_2)))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.43/1.73  tff(c_149, plain, (![A_47]: (k5_relat_1(A_47, k6_partfun1(k2_relat_1(A_47)))=A_47 | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 4.43/1.73  tff(c_158, plain, (k5_relat_1(k1_xboole_0, k6_partfun1(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 4.43/1.73  tff(c_162, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_100, c_158])).
% 4.43/1.73  tff(c_1361, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_875, c_875, c_162])).
% 4.43/1.73  tff(c_1659, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1645, c_1645, c_1361])).
% 4.43/1.73  tff(c_1674, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_196])).
% 4.43/1.73  tff(c_16, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.43/1.73  tff(c_76, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 4.43/1.73  tff(c_116, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_76])).
% 4.43/1.73  tff(c_1366, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_875, c_116])).
% 4.43/1.73  tff(c_1671, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1366])).
% 4.43/1.73  tff(c_1668, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1645, c_1411])).
% 4.43/1.73  tff(c_1368, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_875, c_875, c_100])).
% 4.43/1.73  tff(c_1669, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1645, c_1368])).
% 4.43/1.73  tff(c_18, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k1_relat_1(A_4))!=k5_relat_1(A_4, B_6) | k2_relat_1(A_4)!=k1_relat_1(B_6) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.43/1.73  tff(c_1928, plain, (![A_226, B_227]: (k2_funct_1(A_226)=B_227 | k6_partfun1(k1_relat_1(A_226))!=k5_relat_1(A_226, B_227) | k2_relat_1(A_226)!=k1_relat_1(B_227) | ~v2_funct_1(A_226) | ~v1_funct_1(B_227) | ~v1_relat_1(B_227) | ~v1_funct_1(A_226) | ~v1_relat_1(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 4.43/1.73  tff(c_1930, plain, (![B_227]: (k2_funct_1('#skF_1')=B_227 | k5_relat_1('#skF_1', B_227)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_1')!=k1_relat_1(B_227) | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_227) | ~v1_relat_1(B_227) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1666, c_1928])).
% 4.43/1.73  tff(c_1942, plain, (![B_228]: (k2_funct_1('#skF_1')=B_228 | k5_relat_1('#skF_1', B_228)!='#skF_1' | k1_relat_1(B_228)!='#skF_1' | ~v1_funct_1(B_228) | ~v1_relat_1(B_228))), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_1678, c_1671, c_1668, c_1669, c_1930])).
% 4.43/1.73  tff(c_1945, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k1_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1674, c_1942])).
% 4.43/1.73  tff(c_1951, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1666, c_1659, c_1945])).
% 4.43/1.73  tff(c_1676, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_64])).
% 4.43/1.73  tff(c_1677, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_62])).
% 4.43/1.73  tff(c_1675, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_60])).
% 4.43/1.73  tff(c_1917, plain, (![A_224, B_225]: (k2_funct_2(A_224, B_225)=k2_funct_1(B_225) | ~m1_subset_1(B_225, k1_zfmisc_1(k2_zfmisc_1(A_224, A_224))) | ~v3_funct_2(B_225, A_224, A_224) | ~v1_funct_2(B_225, A_224, A_224) | ~v1_funct_1(B_225))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.43/1.73  tff(c_1920, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1675, c_1917])).
% 4.43/1.73  tff(c_1926, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1678, c_1676, c_1677, c_1920])).
% 4.43/1.73  tff(c_1380, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_56])).
% 4.43/1.73  tff(c_1663, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1645, c_1645, c_1380])).
% 4.43/1.73  tff(c_1937, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_1663])).
% 4.43/1.73  tff(c_1954, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1951, c_1937])).
% 4.43/1.73  tff(c_1958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1772, c_1954])).
% 4.43/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.73  
% 4.43/1.73  Inference rules
% 4.43/1.73  ----------------------
% 4.43/1.73  #Ref     : 0
% 4.43/1.73  #Sup     : 413
% 4.43/1.73  #Fact    : 0
% 4.43/1.73  #Define  : 0
% 4.43/1.73  #Split   : 16
% 4.43/1.73  #Chain   : 0
% 4.43/1.73  #Close   : 0
% 4.43/1.73  
% 4.43/1.73  Ordering : KBO
% 4.43/1.73  
% 4.43/1.73  Simplification rules
% 4.43/1.73  ----------------------
% 4.43/1.73  #Subsume      : 16
% 4.43/1.73  #Demod        : 624
% 4.43/1.73  #Tautology    : 293
% 4.43/1.73  #SimpNegUnit  : 6
% 4.43/1.73  #BackRed      : 109
% 4.43/1.73  
% 4.43/1.73  #Partial instantiations: 0
% 4.43/1.73  #Strategies tried      : 1
% 4.43/1.73  
% 4.43/1.73  Timing (in seconds)
% 4.43/1.73  ----------------------
% 4.43/1.73  Preprocessing        : 0.36
% 4.43/1.73  Parsing              : 0.19
% 4.43/1.73  CNF conversion       : 0.03
% 4.43/1.73  Main loop            : 0.58
% 4.43/1.73  Inferencing          : 0.20
% 4.43/1.73  Reduction            : 0.21
% 4.43/1.73  Demodulation         : 0.16
% 4.43/1.73  BG Simplification    : 0.03
% 4.43/1.73  Subsumption          : 0.08
% 4.43/1.73  Abstraction          : 0.03
% 4.43/1.73  MUC search           : 0.00
% 4.43/1.73  Cooper               : 0.00
% 4.43/1.73  Total                : 1.00
% 4.43/1.73  Index Insertion      : 0.00
% 4.43/1.73  Index Deletion       : 0.00
% 4.43/1.73  Index Matching       : 0.00
% 4.43/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
