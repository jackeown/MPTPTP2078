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
% DateTime   : Thu Dec  3 10:15:56 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  178 (1096 expanded)
%              Number of leaves         :   40 ( 376 expanded)
%              Depth                    :   13
%              Number of atoms          :  305 (3281 expanded)
%              Number of equality atoms :   89 ( 669 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_156,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_90,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_34,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_105,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_113,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_105])).

tff(c_285,plain,(
    ! [A_75,B_76,D_77] :
      ( r2_relset_1(A_75,B_76,D_77,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_290,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_285])).

tff(c_132,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_153,plain,(
    ! [B_49,A_50] :
      ( k2_relat_1(B_49) = A_50
      | ~ v2_funct_2(B_49,A_50)
      | ~ v5_relat_1(B_49,A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_156,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_153])).

tff(c_162,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_156])).

tff(c_166,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_60,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_268,plain,(
    ! [C_72,B_73,A_74] :
      ( v2_funct_2(C_72,B_73)
      | ~ v3_funct_2(C_72,A_74,B_73)
      | ~ v1_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_274,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_268])).

tff(c_280,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_274])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_280])).

tff(c_283,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_131,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_292,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_131])).

tff(c_58,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_360,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_relset_1(A_87,B_88,C_89) = k2_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_366,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_360])).

tff(c_370,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_366])).

tff(c_371,plain,(
    ! [C_90,A_91,B_92] :
      ( v2_funct_1(C_90)
      | ~ v3_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_377,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_371])).

tff(c_383,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_377])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_466,plain,(
    ! [C_116,D_117,B_118,A_119] :
      ( k2_funct_1(C_116) = D_117
      | k1_xboole_0 = B_118
      | k1_xboole_0 = A_119
      | ~ v2_funct_1(C_116)
      | ~ r2_relset_1(A_119,A_119,k1_partfun1(A_119,B_118,B_118,A_119,C_116,D_117),k6_partfun1(A_119))
      | k2_relset_1(A_119,B_118,C_116) != B_118
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k2_zfmisc_1(B_118,A_119)))
      | ~ v1_funct_2(D_117,B_118,A_119)
      | ~ v1_funct_1(D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118)))
      | ~ v1_funct_2(C_116,A_119,B_118)
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_469,plain,
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
    inference(resolution,[status(thm)],[c_44,c_466])).

tff(c_475,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_46,c_370,c_383,c_469])).

tff(c_476,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_475])).

tff(c_421,plain,(
    ! [A_100,B_101] :
      ( k2_funct_2(A_100,B_101) = k2_funct_1(B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100)))
      | ~ v3_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_427,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_421])).

tff(c_433,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_427])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_438,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_42])).

tff(c_478,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_438])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_478])).

tff(c_483,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_484,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_514,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_484])).

tff(c_535,plain,(
    ! [C_123,B_124,A_125] :
      ( v5_relat_1(C_123,B_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_543,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_535])).

tff(c_794,plain,(
    ! [B_161,A_162] :
      ( k2_relat_1(B_161) = A_162
      | ~ v2_funct_2(B_161,A_162)
      | ~ v5_relat_1(B_161,A_162)
      | ~ v1_relat_1(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_800,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_543,c_794])).

tff(c_809,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_514,c_800])).

tff(c_813,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_903,plain,(
    ! [C_178,B_179,A_180] :
      ( v2_funct_2(C_178,B_179)
      | ~ v3_funct_2(C_178,A_180,B_179)
      | ~ v1_funct_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_180,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_909,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_903])).

tff(c_915,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_909])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_915])).

tff(c_918,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_120,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_130,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_485,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_130])).

tff(c_927,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_485])).

tff(c_48,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1004,plain,(
    ! [C_187,B_188,A_189] :
      ( v2_funct_2(C_187,B_188)
      | ~ v3_funct_2(C_187,A_189,B_188)
      | ~ v1_funct_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1007,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1004])).

tff(c_1010,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1007])).

tff(c_542,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_535])).

tff(c_803,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_542,c_794])).

tff(c_812,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_803])).

tff(c_1016,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_812])).

tff(c_1017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_927,c_1016])).

tff(c_1018,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1094,plain,(
    ! [C_195,B_196,A_197] :
      ( v5_relat_1(C_195,B_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1102,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1094])).

tff(c_1267,plain,(
    ! [B_222,A_223] :
      ( k2_relat_1(B_222) = A_223
      | ~ v2_funct_2(B_222,A_223)
      | ~ v5_relat_1(B_222,A_223)
      | ~ v1_relat_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1273,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1102,c_1267])).

tff(c_1282,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1273])).

tff(c_1333,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1282])).

tff(c_1418,plain,(
    ! [C_239,B_240,A_241] :
      ( v2_funct_2(C_239,B_240)
      | ~ v3_funct_2(C_239,A_241,B_240)
      | ~ v1_funct_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1421,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1418])).

tff(c_1424,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1421])).

tff(c_1426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1333,c_1424])).

tff(c_1427,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1282])).

tff(c_1019,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1030,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1019])).

tff(c_1101,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1094])).

tff(c_1276,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1101,c_1267])).

tff(c_1285,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1030,c_1276])).

tff(c_1286,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1285])).

tff(c_1319,plain,(
    ! [C_230,B_231,A_232] :
      ( v2_funct_2(C_230,B_231)
      | ~ v3_funct_2(C_230,A_232,B_231)
      | ~ v1_funct_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1322,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1319])).

tff(c_1328,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1322])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1286,c_1328])).

tff(c_1331,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1285])).

tff(c_1020,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_1068,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1020])).

tff(c_1436,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_1068])).

tff(c_1511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1427,c_1436])).

tff(c_1512,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_1523,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1512])).

tff(c_1513,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_1557,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1018,c_1513])).

tff(c_1577,plain,(
    ! [C_248,B_249,A_250] :
      ( v5_relat_1(C_248,B_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1581,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1577])).

tff(c_1725,plain,(
    ! [B_277,A_278] :
      ( k2_relat_1(B_277) = A_278
      | ~ v2_funct_2(B_277,A_278)
      | ~ v5_relat_1(B_277,A_278)
      | ~ v1_relat_1(B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1731,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1581,c_1725])).

tff(c_1737,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1557,c_1731])).

tff(c_1738,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_1756,plain,(
    ! [C_285,B_286,A_287] :
      ( v2_funct_2(C_285,B_286)
      | ~ v3_funct_2(C_285,A_287,B_286)
      | ~ v1_funct_1(C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1759,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1756])).

tff(c_1762,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1759])).

tff(c_1764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1738,c_1762])).

tff(c_1765,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_1721,plain,(
    ! [A_274,B_275,D_276] :
      ( r2_relset_1(A_274,B_275,D_276,D_276)
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1724,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1721])).

tff(c_1767,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_1765,c_1724])).

tff(c_1786,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_52])).

tff(c_1785,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_50])).

tff(c_1784,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_48])).

tff(c_66,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6])).

tff(c_34,plain,(
    ! [A_23] : k6_relat_1(A_23) = k6_partfun1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_2] : k2_funct_1(k6_relat_1(A_2)) = k6_relat_1(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_86,plain,(
    ! [A_36] : k2_funct_1(k6_partfun1(A_36)) = k6_partfun1(A_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_8])).

tff(c_95,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_86])).

tff(c_98,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_95])).

tff(c_1516,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1018,c_98])).

tff(c_1777,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_1765,c_1516])).

tff(c_1783,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_46])).

tff(c_1914,plain,(
    ! [A_303,B_304] :
      ( k2_funct_2(A_303,B_304) = k2_funct_1(B_304)
      | ~ m1_subset_1(B_304,k1_zfmisc_1(k2_zfmisc_1(A_303,A_303)))
      | ~ v3_funct_2(B_304,A_303,A_303)
      | ~ v1_funct_2(B_304,A_303,A_303)
      | ~ v1_funct_1(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1917,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1783,c_1914])).

tff(c_1920,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1785,c_1784,c_1777,c_1917])).

tff(c_1526,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_42])).

tff(c_1776,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_1765,c_1526])).

tff(c_1921,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_1776])).

tff(c_1924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.65  
% 3.98/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.66  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.98/1.66  
% 3.98/1.66  %Foreground sorts:
% 3.98/1.66  
% 3.98/1.66  
% 3.98/1.66  %Background operators:
% 3.98/1.66  
% 3.98/1.66  
% 3.98/1.66  %Foreground operators:
% 3.98/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/1.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.98/1.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.66  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.98/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.66  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.98/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.98/1.66  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.66  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.98/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.98/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.66  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.98/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.98/1.66  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.98/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.66  
% 3.98/1.68  tff(f_156, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 3.98/1.68  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.98/1.68  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.98/1.68  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.98/1.68  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.98/1.68  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.98/1.68  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.98/1.68  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.98/1.68  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.98/1.68  tff(f_88, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.98/1.68  tff(f_90, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.98/1.68  tff(f_34, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.98/1.68  tff(f_36, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.98/1.68  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_105, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.98/1.68  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_105])).
% 3.98/1.68  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_113, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_105])).
% 3.98/1.68  tff(c_285, plain, (![A_75, B_76, D_77]: (r2_relset_1(A_75, B_76, D_77, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.68  tff(c_290, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_285])).
% 3.98/1.68  tff(c_132, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.98/1.68  tff(c_140, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_132])).
% 3.98/1.68  tff(c_153, plain, (![B_49, A_50]: (k2_relat_1(B_49)=A_50 | ~v2_funct_2(B_49, A_50) | ~v5_relat_1(B_49, A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.68  tff(c_156, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_140, c_153])).
% 3.98/1.68  tff(c_162, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_156])).
% 3.98/1.68  tff(c_166, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_162])).
% 3.98/1.68  tff(c_60, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_56, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_268, plain, (![C_72, B_73, A_74]: (v2_funct_2(C_72, B_73) | ~v3_funct_2(C_72, A_74, B_73) | ~v1_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_274, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_268])).
% 3.98/1.68  tff(c_280, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_274])).
% 3.98/1.68  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_280])).
% 3.98/1.68  tff(c_283, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_162])).
% 3.98/1.68  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.68  tff(c_128, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.98/1.68  tff(c_131, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 3.98/1.68  tff(c_292, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_131])).
% 3.98/1.68  tff(c_58, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_360, plain, (![A_87, B_88, C_89]: (k2_relset_1(A_87, B_88, C_89)=k2_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.98/1.68  tff(c_366, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_360])).
% 3.98/1.68  tff(c_370, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_366])).
% 3.98/1.68  tff(c_371, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_377, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_371])).
% 3.98/1.68  tff(c_383, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_377])).
% 3.98/1.68  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_466, plain, (![C_116, D_117, B_118, A_119]: (k2_funct_1(C_116)=D_117 | k1_xboole_0=B_118 | k1_xboole_0=A_119 | ~v2_funct_1(C_116) | ~r2_relset_1(A_119, A_119, k1_partfun1(A_119, B_118, B_118, A_119, C_116, D_117), k6_partfun1(A_119)) | k2_relset_1(A_119, B_118, C_116)!=B_118 | ~m1_subset_1(D_117, k1_zfmisc_1(k2_zfmisc_1(B_118, A_119))) | ~v1_funct_2(D_117, B_118, A_119) | ~v1_funct_1(D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))) | ~v1_funct_2(C_116, A_119, B_118) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.98/1.68  tff(c_469, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_466])).
% 3.98/1.68  tff(c_475, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_46, c_370, c_383, c_469])).
% 3.98/1.68  tff(c_476, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_292, c_475])).
% 3.98/1.68  tff(c_421, plain, (![A_100, B_101]: (k2_funct_2(A_100, B_101)=k2_funct_1(B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))) | ~v3_funct_2(B_101, A_100, A_100) | ~v1_funct_2(B_101, A_100, A_100) | ~v1_funct_1(B_101))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.98/1.68  tff(c_427, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_421])).
% 3.98/1.68  tff(c_433, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_427])).
% 3.98/1.68  tff(c_42, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_438, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_42])).
% 3.98/1.68  tff(c_478, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_438])).
% 3.98/1.68  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_478])).
% 3.98/1.68  tff(c_483, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_128])).
% 3.98/1.68  tff(c_484, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 3.98/1.68  tff(c_514, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_483, c_484])).
% 3.98/1.68  tff(c_535, plain, (![C_123, B_124, A_125]: (v5_relat_1(C_123, B_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.98/1.68  tff(c_543, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_535])).
% 3.98/1.68  tff(c_794, plain, (![B_161, A_162]: (k2_relat_1(B_161)=A_162 | ~v2_funct_2(B_161, A_162) | ~v5_relat_1(B_161, A_162) | ~v1_relat_1(B_161))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.68  tff(c_800, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_543, c_794])).
% 3.98/1.68  tff(c_809, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_514, c_800])).
% 3.98/1.68  tff(c_813, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_809])).
% 3.98/1.68  tff(c_903, plain, (![C_178, B_179, A_180]: (v2_funct_2(C_178, B_179) | ~v3_funct_2(C_178, A_180, B_179) | ~v1_funct_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_180, B_179))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_909, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_903])).
% 3.98/1.68  tff(c_915, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_909])).
% 3.98/1.68  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_813, c_915])).
% 3.98/1.68  tff(c_918, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_809])).
% 3.98/1.68  tff(c_120, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_112, c_2])).
% 3.98/1.68  tff(c_130, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_120])).
% 3.98/1.68  tff(c_485, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_483, c_130])).
% 3.98/1.68  tff(c_927, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_918, c_485])).
% 3.98/1.68  tff(c_48, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.98/1.68  tff(c_1004, plain, (![C_187, B_188, A_189]: (v2_funct_2(C_187, B_188) | ~v3_funct_2(C_187, A_189, B_188) | ~v1_funct_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_1007, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1004])).
% 3.98/1.68  tff(c_1010, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1007])).
% 3.98/1.68  tff(c_542, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_535])).
% 3.98/1.68  tff(c_803, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_542, c_794])).
% 3.98/1.68  tff(c_812, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_803])).
% 3.98/1.68  tff(c_1016, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_812])).
% 3.98/1.68  tff(c_1017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_927, c_1016])).
% 3.98/1.68  tff(c_1018, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_120])).
% 3.98/1.68  tff(c_1094, plain, (![C_195, B_196, A_197]: (v5_relat_1(C_195, B_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.98/1.68  tff(c_1102, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_1094])).
% 3.98/1.68  tff(c_1267, plain, (![B_222, A_223]: (k2_relat_1(B_222)=A_223 | ~v2_funct_2(B_222, A_223) | ~v5_relat_1(B_222, A_223) | ~v1_relat_1(B_222))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.68  tff(c_1273, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1102, c_1267])).
% 3.98/1.68  tff(c_1282, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1273])).
% 3.98/1.68  tff(c_1333, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1282])).
% 3.98/1.68  tff(c_1418, plain, (![C_239, B_240, A_241]: (v2_funct_2(C_239, B_240) | ~v3_funct_2(C_239, A_241, B_240) | ~v1_funct_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_1421, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1418])).
% 3.98/1.68  tff(c_1424, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1421])).
% 3.98/1.68  tff(c_1426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1333, c_1424])).
% 3.98/1.68  tff(c_1427, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1282])).
% 3.98/1.68  tff(c_1019, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_120])).
% 3.98/1.68  tff(c_1030, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1019])).
% 3.98/1.68  tff(c_1101, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_1094])).
% 3.98/1.68  tff(c_1276, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1101, c_1267])).
% 3.98/1.68  tff(c_1285, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1030, c_1276])).
% 3.98/1.68  tff(c_1286, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1285])).
% 3.98/1.68  tff(c_1319, plain, (![C_230, B_231, A_232]: (v2_funct_2(C_230, B_231) | ~v3_funct_2(C_230, A_232, B_231) | ~v1_funct_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_1322, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1319])).
% 3.98/1.68  tff(c_1328, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1322])).
% 3.98/1.68  tff(c_1330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1286, c_1328])).
% 3.98/1.68  tff(c_1331, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1285])).
% 3.98/1.68  tff(c_1020, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 3.98/1.68  tff(c_1068, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1020])).
% 3.98/1.68  tff(c_1436, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_1068])).
% 3.98/1.68  tff(c_1511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1427, c_1436])).
% 3.98/1.68  tff(c_1512, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_128])).
% 3.98/1.68  tff(c_1523, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1512])).
% 3.98/1.68  tff(c_1513, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 3.98/1.68  tff(c_1557, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1018, c_1513])).
% 3.98/1.68  tff(c_1577, plain, (![C_248, B_249, A_250]: (v5_relat_1(C_248, B_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.98/1.68  tff(c_1581, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_1577])).
% 3.98/1.68  tff(c_1725, plain, (![B_277, A_278]: (k2_relat_1(B_277)=A_278 | ~v2_funct_2(B_277, A_278) | ~v5_relat_1(B_277, A_278) | ~v1_relat_1(B_277))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.68  tff(c_1731, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1581, c_1725])).
% 3.98/1.68  tff(c_1737, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1557, c_1731])).
% 3.98/1.68  tff(c_1738, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1737])).
% 3.98/1.68  tff(c_1756, plain, (![C_285, B_286, A_287]: (v2_funct_2(C_285, B_286) | ~v3_funct_2(C_285, A_287, B_286) | ~v1_funct_1(C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_286))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.68  tff(c_1759, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1756])).
% 3.98/1.68  tff(c_1762, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1759])).
% 3.98/1.68  tff(c_1764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1738, c_1762])).
% 3.98/1.68  tff(c_1765, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1737])).
% 3.98/1.68  tff(c_1721, plain, (![A_274, B_275, D_276]: (r2_relset_1(A_274, B_275, D_276, D_276) | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.68  tff(c_1724, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1721])).
% 3.98/1.68  tff(c_1767, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_1765, c_1724])).
% 3.98/1.68  tff(c_1786, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_52])).
% 3.98/1.68  tff(c_1785, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_50])).
% 3.98/1.68  tff(c_1784, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_48])).
% 3.98/1.68  tff(c_66, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.98/1.68  tff(c_6, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.68  tff(c_72, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_66, c_6])).
% 3.98/1.68  tff(c_34, plain, (![A_23]: (k6_relat_1(A_23)=k6_partfun1(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.98/1.68  tff(c_8, plain, (![A_2]: (k2_funct_1(k6_relat_1(A_2))=k6_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.98/1.68  tff(c_86, plain, (![A_36]: (k2_funct_1(k6_partfun1(A_36))=k6_partfun1(A_36))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_8])).
% 3.98/1.68  tff(c_95, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_86])).
% 3.98/1.68  tff(c_98, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_95])).
% 3.98/1.68  tff(c_1516, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1018, c_98])).
% 3.98/1.68  tff(c_1777, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_1765, c_1516])).
% 3.98/1.68  tff(c_1783, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_46])).
% 3.98/1.68  tff(c_1914, plain, (![A_303, B_304]: (k2_funct_2(A_303, B_304)=k2_funct_1(B_304) | ~m1_subset_1(B_304, k1_zfmisc_1(k2_zfmisc_1(A_303, A_303))) | ~v3_funct_2(B_304, A_303, A_303) | ~v1_funct_2(B_304, A_303, A_303) | ~v1_funct_1(B_304))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.98/1.68  tff(c_1917, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1783, c_1914])).
% 3.98/1.68  tff(c_1920, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1785, c_1784, c_1777, c_1917])).
% 3.98/1.68  tff(c_1526, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_42])).
% 3.98/1.68  tff(c_1776, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_1765, c_1526])).
% 3.98/1.68  tff(c_1921, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_1776])).
% 3.98/1.68  tff(c_1924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1921])).
% 3.98/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.68  
% 3.98/1.68  Inference rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Ref     : 0
% 3.98/1.68  #Sup     : 412
% 3.98/1.68  #Fact    : 0
% 3.98/1.68  #Define  : 0
% 3.98/1.68  #Split   : 26
% 3.98/1.68  #Chain   : 0
% 3.98/1.68  #Close   : 0
% 3.98/1.68  
% 3.98/1.68  Ordering : KBO
% 3.98/1.68  
% 3.98/1.68  Simplification rules
% 3.98/1.68  ----------------------
% 3.98/1.68  #Subsume      : 5
% 3.98/1.68  #Demod        : 590
% 3.98/1.68  #Tautology    : 280
% 3.98/1.68  #SimpNegUnit  : 14
% 3.98/1.68  #BackRed      : 173
% 3.98/1.68  
% 3.98/1.68  #Partial instantiations: 0
% 3.98/1.68  #Strategies tried      : 1
% 3.98/1.68  
% 3.98/1.68  Timing (in seconds)
% 3.98/1.68  ----------------------
% 3.98/1.69  Preprocessing        : 0.34
% 3.98/1.69  Parsing              : 0.18
% 3.98/1.69  CNF conversion       : 0.02
% 3.98/1.69  Main loop            : 0.56
% 3.98/1.69  Inferencing          : 0.20
% 3.98/1.69  Reduction            : 0.19
% 3.98/1.69  Demodulation         : 0.14
% 3.98/1.69  BG Simplification    : 0.02
% 3.98/1.69  Subsumption          : 0.07
% 3.98/1.69  Abstraction          : 0.02
% 3.98/1.69  MUC search           : 0.00
% 3.98/1.69  Cooper               : 0.00
% 3.98/1.69  Total                : 0.97
% 3.98/1.69  Index Insertion      : 0.00
% 3.98/1.69  Index Deletion       : 0.00
% 3.98/1.69  Index Matching       : 0.00
% 3.98/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
