%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:54 EST 2020

% Result     : Theorem 5.53s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  226 (3265 expanded)
%              Number of leaves         :   46 (1069 expanded)
%              Depth                    :   16
%              Number of atoms          :  456 (9792 expanded)
%              Number of equality atoms :  136 (2078 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_200,negated_conjecture,(
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

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_88,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_178,axiom,(
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

tff(f_132,axiom,(
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

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_118,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_134,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_243,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_255,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_243])).

tff(c_201,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_217,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_201])).

tff(c_265,plain,(
    ! [B_74,A_75] :
      ( k2_relat_1(B_74) = A_75
      | ~ v2_funct_2(B_74,A_75)
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_274,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_217,c_265])).

tff(c_286,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_274])).

tff(c_320,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_436,plain,(
    ! [C_91,B_92,A_93] :
      ( v2_funct_2(C_91,B_92)
      | ~ v3_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_448,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_436])).

tff(c_457,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_448])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_457])).

tff(c_460,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_6,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_150,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_134,c_6])).

tff(c_199,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_463,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_199])).

tff(c_74,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_72,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_133,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_118])).

tff(c_216,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_201])).

tff(c_277,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_216,c_265])).

tff(c_289,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_277])).

tff(c_499,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_70,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_525,plain,(
    ! [C_100,B_101,A_102] :
      ( v2_funct_2(C_100,B_101)
      | ~ v3_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_534,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_525])).

tff(c_543,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_534])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_543])).

tff(c_546,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_290,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_306,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_290])).

tff(c_548,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_306])).

tff(c_42,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_253,plain,(
    ! [A_29] : r2_relset_1(A_29,A_29,k6_partfun1(A_29),k6_partfun1(A_29)) ),
    inference(resolution,[status(thm)],[c_42,c_243])).

tff(c_478,plain,(
    ! [C_94,A_95,B_96] :
      ( v2_funct_1(C_94)
      | ~ v3_funct_2(C_94,A_95,B_96)
      | ~ v1_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_487,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_478])).

tff(c_495,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_487])).

tff(c_820,plain,(
    ! [C_137,D_142,F_139,B_138,E_141,A_140] :
      ( k1_partfun1(A_140,B_138,C_137,D_142,E_141,F_139) = k5_relat_1(E_141,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_137,D_142)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_828,plain,(
    ! [A_140,B_138,E_141] :
      ( k1_partfun1(A_140,B_138,'#skF_1','#skF_1',E_141,'#skF_3') = k5_relat_1(E_141,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(resolution,[status(thm)],[c_60,c_820])).

tff(c_872,plain,(
    ! [A_147,B_148,E_149] :
      ( k1_partfun1(A_147,B_148,'#skF_1','#skF_1',E_149,'#skF_3') = k5_relat_1(E_149,'#skF_3')
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_funct_1(E_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_828])).

tff(c_881,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_872])).

tff(c_889,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_881])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_616,plain,(
    ! [D_110,C_111,A_112,B_113] :
      ( D_110 = C_111
      | ~ r2_relset_1(A_112,B_113,C_111,D_110)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_626,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_616])).

tff(c_645,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_626])).

tff(c_681,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_894,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_681])).

tff(c_900,plain,(
    ! [E_152,A_155,B_153,F_151,C_150,D_154] :
      ( m1_subset_1(k1_partfun1(A_155,B_153,C_150,D_154,E_152,F_151),k1_zfmisc_1(k2_zfmisc_1(A_155,D_154)))
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_150,D_154)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_155,B_153)))
      | ~ v1_funct_1(E_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_943,plain,
    ( m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_900])).

tff(c_965,plain,(
    m1_subset_1(k5_relat_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_66,c_60,c_943])).

tff(c_975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_965])).

tff(c_976,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_1634,plain,(
    ! [C_201,D_202,B_203,A_204] :
      ( k2_funct_1(C_201) = D_202
      | k1_xboole_0 = B_203
      | k1_xboole_0 = A_204
      | ~ v2_funct_1(C_201)
      | ~ r2_relset_1(A_204,A_204,k1_partfun1(A_204,B_203,B_203,A_204,C_201,D_202),k6_partfun1(A_204))
      | k2_relset_1(A_204,B_203,C_201) != B_203
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(B_203,A_204)))
      | ~ v1_funct_2(D_202,B_203,A_204)
      | ~ v1_funct_1(D_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_2(C_201,A_204,B_203)
      | ~ v1_funct_1(C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1646,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1634])).

tff(c_1660,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_64,c_60,c_548,c_253,c_495,c_1646])).

tff(c_1661,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_1660])).

tff(c_646,plain,(
    ! [A_114,B_115] :
      ( k2_funct_2(A_114,B_115) = k2_funct_1(B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_zfmisc_1(A_114,A_114)))
      | ~ v3_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_655,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_646])).

tff(c_663,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_655])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_667,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_56])).

tff(c_1664,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1661,c_667])).

tff(c_1668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1664])).

tff(c_1669,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1670,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1686,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1670])).

tff(c_2317,plain,(
    ! [C_257,B_258,A_259] :
      ( v5_relat_1(C_257,B_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_259,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2325,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_2317])).

tff(c_2416,plain,(
    ! [B_268,A_269] :
      ( k2_relat_1(B_268) = A_269
      | ~ v2_funct_2(B_268,A_269)
      | ~ v5_relat_1(B_268,A_269)
      | ~ v1_relat_1(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2425,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2325,c_2416])).

tff(c_2434,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1686,c_2425])).

tff(c_2435,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2434])).

tff(c_2521,plain,(
    ! [C_281,B_282,A_283] :
      ( v2_funct_2(C_281,B_282)
      | ~ v3_funct_2(C_281,A_283,B_282)
      | ~ v1_funct_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_283,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2530,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2521])).

tff(c_2537,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2530])).

tff(c_2539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2435,c_2537])).

tff(c_2540,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2434])).

tff(c_2397,plain,(
    ! [A_264,B_265,D_266] :
      ( r2_relset_1(A_264,B_265,D_266,D_266)
      | ~ m1_subset_1(D_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2406,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2397])).

tff(c_2558,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_2540,c_2406])).

tff(c_2580,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_66])).

tff(c_2573,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_2540,c_1686])).

tff(c_2576,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_134])).

tff(c_2579,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_62])).

tff(c_2577,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_60])).

tff(c_28,plain,(
    ! [C_20,A_18,B_19] :
      ( v2_funct_1(C_20)
      | ~ v3_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2694,plain,
    ( v2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2577,c_28])).

tff(c_2714,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2579,c_2694])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1679,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1669,c_4])).

tff(c_1724,plain,(
    ! [C_205,B_206,A_207] :
      ( v5_relat_1(C_205,B_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1736,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1724])).

tff(c_1800,plain,(
    ! [B_215,A_216] :
      ( k2_relat_1(B_215) = A_216
      | ~ v2_funct_2(B_215,A_216)
      | ~ v5_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1809,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1736,c_1800])).

tff(c_1821,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1686,c_1809])).

tff(c_1825,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1821])).

tff(c_2081,plain,(
    ! [C_241,B_242,A_243] :
      ( v2_funct_2(C_241,B_242)
      | ~ v3_funct_2(C_241,A_243,B_242)
      | ~ v1_funct_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_243,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2093,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2081])).

tff(c_2103,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2093])).

tff(c_2105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_2103])).

tff(c_2106,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1821])).

tff(c_142,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_1753,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1669,c_142])).

tff(c_1754,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1753])).

tff(c_2133,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_1754])).

tff(c_2225,plain,(
    ! [C_250,B_251,A_252] :
      ( v2_funct_2(C_250,B_251)
      | ~ v3_funct_2(C_250,A_252,B_251)
      | ~ v1_funct_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2231,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2225])).

tff(c_2235,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2231])).

tff(c_1735,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1724])).

tff(c_1812,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1735,c_1800])).

tff(c_1824,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_1812])).

tff(c_2263,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2235,c_1824])).

tff(c_2264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2133,c_2263])).

tff(c_2265,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1753])).

tff(c_8,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_141,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_133,c_8])).

tff(c_1691,plain,
    ( k1_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1669,c_141])).

tff(c_1692,plain,(
    k1_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1691])).

tff(c_2267,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_1692])).

tff(c_2279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1679,c_2267])).

tff(c_2280,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_2281,plain,(
    k1_relat_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_2300,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_2281])).

tff(c_2571,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_2540,c_2300])).

tff(c_89,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10])).

tff(c_1677,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1669,c_95])).

tff(c_2567,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_2540,c_1677])).

tff(c_48,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_12,plain,(
    ! [A_2,B_4] :
      ( k2_funct_1(A_2) = B_4
      | k6_relat_1(k2_relat_1(A_2)) != k5_relat_1(B_4,A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2815,plain,(
    ! [A_306,B_307] :
      ( k2_funct_1(A_306) = B_307
      | k6_partfun1(k2_relat_1(A_306)) != k5_relat_1(B_307,A_306)
      | k2_relat_1(B_307) != k1_relat_1(A_306)
      | ~ v2_funct_1(A_306)
      | ~ v1_funct_1(B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_funct_1(A_306)
      | ~ v1_relat_1(A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_2817,plain,(
    ! [B_307] :
      ( k2_funct_1('#skF_1') = B_307
      | k5_relat_1(B_307,'#skF_1') != k6_partfun1('#skF_1')
      | k2_relat_1(B_307) != k1_relat_1('#skF_1')
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_307)
      | ~ v1_relat_1(B_307)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2573,c_2815])).

tff(c_2826,plain,(
    ! [B_309] :
      ( k2_funct_1('#skF_1') = B_309
      | k5_relat_1(B_309,'#skF_1') != '#skF_1'
      | k2_relat_1(B_309) != '#skF_1'
      | ~ v1_funct_1(B_309)
      | ~ v1_relat_1(B_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2576,c_2580,c_2714,c_2571,c_2567,c_2817])).

tff(c_2829,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2576,c_2826])).

tff(c_2835,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2573,c_2829])).

tff(c_2837,plain,(
    k5_relat_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2835])).

tff(c_2860,plain,(
    ! [C_318,A_321,F_320,E_322,D_323,B_319] :
      ( k1_partfun1(A_321,B_319,C_318,D_323,E_322,F_320) = k5_relat_1(E_322,F_320)
      | ~ m1_subset_1(F_320,k1_zfmisc_1(k2_zfmisc_1(C_318,D_323)))
      | ~ v1_funct_1(F_320)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(A_321,B_319)))
      | ~ v1_funct_1(E_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2862,plain,(
    ! [A_321,B_319,E_322] :
      ( k1_partfun1(A_321,B_319,'#skF_1','#skF_1',E_322,'#skF_1') = k5_relat_1(E_322,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(A_321,B_319)))
      | ~ v1_funct_1(E_322) ) ),
    inference(resolution,[status(thm)],[c_2577,c_2860])).

tff(c_2886,plain,(
    ! [A_328,B_329,E_330] :
      ( k1_partfun1(A_328,B_329,'#skF_1','#skF_1',E_330,'#skF_1') = k5_relat_1(E_330,'#skF_1')
      | ~ m1_subset_1(E_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329)))
      | ~ v1_funct_1(E_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2862])).

tff(c_2889,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2577,c_2886])).

tff(c_2895,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2889])).

tff(c_2284,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_58])).

tff(c_2563,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_2540,c_2284])).

tff(c_2771,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2567,c_2563])).

tff(c_24,plain,(
    ! [D_17,C_16,A_14,B_15] :
      ( D_17 = C_16
      | ~ r2_relset_1(A_14,B_15,C_16,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2773,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2771,c_24])).

tff(c_2776,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2577,c_2773])).

tff(c_2850,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2776])).

tff(c_2898,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2895,c_2850])).

tff(c_2910,plain,(
    ! [C_331,D_335,B_334,A_336,F_332,E_333] :
      ( m1_subset_1(k1_partfun1(A_336,B_334,C_331,D_335,E_333,F_332),k1_zfmisc_1(k2_zfmisc_1(A_336,D_335)))
      | ~ m1_subset_1(F_332,k1_zfmisc_1(k2_zfmisc_1(C_331,D_335)))
      | ~ v1_funct_1(F_332)
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_336,B_334)))
      | ~ v1_funct_1(E_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2947,plain,
    ( m1_subset_1(k5_relat_1('#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_1')
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2895,c_2910])).

tff(c_2961,plain,(
    m1_subset_1(k5_relat_1('#skF_1','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2577,c_2580,c_2577,c_2947])).

tff(c_2963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2898,c_2961])).

tff(c_2964,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2776])).

tff(c_3025,plain,(
    ! [C_354,B_355,A_357,E_358,D_359,F_356] :
      ( k1_partfun1(A_357,B_355,C_354,D_359,E_358,F_356) = k5_relat_1(E_358,F_356)
      | ~ m1_subset_1(F_356,k1_zfmisc_1(k2_zfmisc_1(C_354,D_359)))
      | ~ v1_funct_1(F_356)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_357,B_355)))
      | ~ v1_funct_1(E_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3027,plain,(
    ! [A_357,B_355,E_358] :
      ( k1_partfun1(A_357,B_355,'#skF_1','#skF_1',E_358,'#skF_1') = k5_relat_1(E_358,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_357,B_355)))
      | ~ v1_funct_1(E_358) ) ),
    inference(resolution,[status(thm)],[c_2577,c_3025])).

tff(c_3085,plain,(
    ! [A_366,B_367,E_368] :
      ( k1_partfun1(A_366,B_367,'#skF_1','#skF_1',E_368,'#skF_1') = k5_relat_1(E_368,'#skF_1')
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367)))
      | ~ v1_funct_1(E_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_3027])).

tff(c_3091,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = k5_relat_1('#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2577,c_3085])).

tff(c_3098,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2964,c_3091])).

tff(c_3100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2837,c_3098])).

tff(c_3101,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2835])).

tff(c_2578,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_64])).

tff(c_2742,plain,(
    ! [A_299,B_300] :
      ( k2_funct_2(A_299,B_300) = k2_funct_1(B_300)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(k2_zfmisc_1(A_299,A_299)))
      | ~ v3_funct_2(B_300,A_299,A_299)
      | ~ v1_funct_2(B_300,A_299,A_299)
      | ~ v1_funct_1(B_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2745,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2577,c_2742])).

tff(c_2751,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2580,c_2578,c_2579,c_2745])).

tff(c_2285,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_56])).

tff(c_2566,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2540,c_2540,c_2285])).

tff(c_2753,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_2566])).

tff(c_3104,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3101,c_2753])).

tff(c_3108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_3104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:46:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.53/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.13  
% 5.69/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.13  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.69/2.13  
% 5.69/2.13  %Foreground sorts:
% 5.69/2.13  
% 5.69/2.13  
% 5.69/2.13  %Background operators:
% 5.69/2.13  
% 5.69/2.13  
% 5.69/2.13  %Foreground operators:
% 5.69/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.69/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.69/2.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.69/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.69/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.13  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.69/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.69/2.13  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.69/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.69/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.69/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.69/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.69/2.13  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.69/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.69/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.69/2.13  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.69/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.69/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.13  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.69/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.69/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.69/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.69/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.69/2.13  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.69/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.69/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.13  
% 5.69/2.17  tff(f_200, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 5.69/2.17  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.69/2.17  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.69/2.17  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.69/2.17  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.69/2.17  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.69/2.17  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.69/2.17  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.69/2.17  tff(f_112, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.69/2.17  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.69/2.17  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.69/2.17  tff(f_178, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.69/2.17  tff(f_132, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.69/2.17  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.69/2.17  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.69/2.17  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 5.69/2.17  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 5.69/2.17  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_118, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.69/2.17  tff(c_134, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_118])).
% 5.69/2.17  tff(c_243, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.69/2.17  tff(c_255, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_243])).
% 5.69/2.17  tff(c_201, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.17  tff(c_217, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_201])).
% 5.69/2.17  tff(c_265, plain, (![B_74, A_75]: (k2_relat_1(B_74)=A_75 | ~v2_funct_2(B_74, A_75) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.69/2.17  tff(c_274, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_217, c_265])).
% 5.69/2.17  tff(c_286, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_274])).
% 5.69/2.17  tff(c_320, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_286])).
% 5.69/2.17  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_436, plain, (![C_91, B_92, A_93]: (v2_funct_2(C_91, B_92) | ~v3_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_448, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_436])).
% 5.69/2.17  tff(c_457, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_448])).
% 5.69/2.17  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_457])).
% 5.69/2.17  tff(c_460, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_286])).
% 5.69/2.17  tff(c_6, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.17  tff(c_150, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_134, c_6])).
% 5.69/2.17  tff(c_199, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 5.69/2.17  tff(c_463, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_199])).
% 5.69/2.17  tff(c_74, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_72, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_133, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_118])).
% 5.69/2.17  tff(c_216, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_201])).
% 5.69/2.17  tff(c_277, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_216, c_265])).
% 5.69/2.17  tff(c_289, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_277])).
% 5.69/2.17  tff(c_499, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_289])).
% 5.69/2.17  tff(c_70, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_525, plain, (![C_100, B_101, A_102]: (v2_funct_2(C_100, B_101) | ~v3_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_534, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_525])).
% 5.69/2.17  tff(c_543, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_534])).
% 5.69/2.17  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_543])).
% 5.69/2.17  tff(c_546, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_289])).
% 5.69/2.17  tff(c_290, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.69/2.17  tff(c_306, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_290])).
% 5.69/2.17  tff(c_548, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_306])).
% 5.69/2.17  tff(c_42, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.69/2.17  tff(c_253, plain, (![A_29]: (r2_relset_1(A_29, A_29, k6_partfun1(A_29), k6_partfun1(A_29)))), inference(resolution, [status(thm)], [c_42, c_243])).
% 5.69/2.17  tff(c_478, plain, (![C_94, A_95, B_96]: (v2_funct_1(C_94) | ~v3_funct_2(C_94, A_95, B_96) | ~v1_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_487, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_478])).
% 5.69/2.17  tff(c_495, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_487])).
% 5.69/2.17  tff(c_820, plain, (![C_137, D_142, F_139, B_138, E_141, A_140]: (k1_partfun1(A_140, B_138, C_137, D_142, E_141, F_139)=k5_relat_1(E_141, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_137, D_142))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.69/2.17  tff(c_828, plain, (![A_140, B_138, E_141]: (k1_partfun1(A_140, B_138, '#skF_1', '#skF_1', E_141, '#skF_3')=k5_relat_1(E_141, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))) | ~v1_funct_1(E_141))), inference(resolution, [status(thm)], [c_60, c_820])).
% 5.69/2.17  tff(c_872, plain, (![A_147, B_148, E_149]: (k1_partfun1(A_147, B_148, '#skF_1', '#skF_1', E_149, '#skF_3')=k5_relat_1(E_149, '#skF_3') | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_funct_1(E_149))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_828])).
% 5.69/2.17  tff(c_881, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_872])).
% 5.69/2.17  tff(c_889, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_881])).
% 5.69/2.17  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_616, plain, (![D_110, C_111, A_112, B_113]: (D_110=C_111 | ~r2_relset_1(A_112, B_113, C_111, D_110) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.69/2.17  tff(c_626, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_616])).
% 5.69/2.17  tff(c_645, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_626])).
% 5.69/2.17  tff(c_681, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_645])).
% 5.69/2.17  tff(c_894, plain, (~m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_681])).
% 5.69/2.17  tff(c_900, plain, (![E_152, A_155, B_153, F_151, C_150, D_154]: (m1_subset_1(k1_partfun1(A_155, B_153, C_150, D_154, E_152, F_151), k1_zfmisc_1(k2_zfmisc_1(A_155, D_154))) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_150, D_154))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(A_155, B_153))) | ~v1_funct_1(E_152))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.69/2.17  tff(c_943, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_889, c_900])).
% 5.69/2.17  tff(c_965, plain, (m1_subset_1(k5_relat_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_66, c_60, c_943])).
% 5.69/2.17  tff(c_975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_894, c_965])).
% 5.69/2.17  tff(c_976, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_645])).
% 5.69/2.17  tff(c_1634, plain, (![C_201, D_202, B_203, A_204]: (k2_funct_1(C_201)=D_202 | k1_xboole_0=B_203 | k1_xboole_0=A_204 | ~v2_funct_1(C_201) | ~r2_relset_1(A_204, A_204, k1_partfun1(A_204, B_203, B_203, A_204, C_201, D_202), k6_partfun1(A_204)) | k2_relset_1(A_204, B_203, C_201)!=B_203 | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(B_203, A_204))) | ~v1_funct_2(D_202, B_203, A_204) | ~v1_funct_1(D_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_2(C_201, A_204, B_203) | ~v1_funct_1(C_201))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.69/2.17  tff(c_1646, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_976, c_1634])).
% 5.69/2.17  tff(c_1660, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_64, c_60, c_548, c_253, c_495, c_1646])).
% 5.69/2.17  tff(c_1661, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_463, c_1660])).
% 5.69/2.17  tff(c_646, plain, (![A_114, B_115]: (k2_funct_2(A_114, B_115)=k2_funct_1(B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_zfmisc_1(A_114, A_114))) | ~v3_funct_2(B_115, A_114, A_114) | ~v1_funct_2(B_115, A_114, A_114) | ~v1_funct_1(B_115))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.69/2.17  tff(c_655, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_646])).
% 5.69/2.17  tff(c_663, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_655])).
% 5.69/2.17  tff(c_56, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.69/2.17  tff(c_667, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_663, c_56])).
% 5.69/2.17  tff(c_1664, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1661, c_667])).
% 5.69/2.17  tff(c_1668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_1664])).
% 5.69/2.17  tff(c_1669, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_150])).
% 5.69/2.17  tff(c_1670, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_150])).
% 5.69/2.17  tff(c_1686, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1670])).
% 5.69/2.17  tff(c_2317, plain, (![C_257, B_258, A_259]: (v5_relat_1(C_257, B_258) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_259, B_258))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.17  tff(c_2325, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_2317])).
% 5.69/2.17  tff(c_2416, plain, (![B_268, A_269]: (k2_relat_1(B_268)=A_269 | ~v2_funct_2(B_268, A_269) | ~v5_relat_1(B_268, A_269) | ~v1_relat_1(B_268))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.69/2.17  tff(c_2425, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2325, c_2416])).
% 5.69/2.17  tff(c_2434, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1686, c_2425])).
% 5.69/2.17  tff(c_2435, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2434])).
% 5.69/2.17  tff(c_2521, plain, (![C_281, B_282, A_283]: (v2_funct_2(C_281, B_282) | ~v3_funct_2(C_281, A_283, B_282) | ~v1_funct_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_283, B_282))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_2530, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2521])).
% 5.69/2.17  tff(c_2537, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2530])).
% 5.69/2.17  tff(c_2539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2435, c_2537])).
% 5.69/2.17  tff(c_2540, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2434])).
% 5.69/2.17  tff(c_2397, plain, (![A_264, B_265, D_266]: (r2_relset_1(A_264, B_265, D_266, D_266) | ~m1_subset_1(D_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.69/2.17  tff(c_2406, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_2397])).
% 5.69/2.17  tff(c_2558, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_2540, c_2406])).
% 5.69/2.17  tff(c_2580, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_66])).
% 5.69/2.17  tff(c_2573, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_2540, c_1686])).
% 5.69/2.17  tff(c_2576, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_134])).
% 5.69/2.17  tff(c_2579, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_62])).
% 5.69/2.17  tff(c_2577, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_60])).
% 5.69/2.17  tff(c_28, plain, (![C_20, A_18, B_19]: (v2_funct_1(C_20) | ~v3_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_2694, plain, (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2577, c_28])).
% 5.69/2.17  tff(c_2714, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2579, c_2694])).
% 5.69/2.17  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.69/2.17  tff(c_1679, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1669, c_4])).
% 5.69/2.17  tff(c_1724, plain, (![C_205, B_206, A_207]: (v5_relat_1(C_205, B_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.17  tff(c_1736, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1724])).
% 5.69/2.17  tff(c_1800, plain, (![B_215, A_216]: (k2_relat_1(B_215)=A_216 | ~v2_funct_2(B_215, A_216) | ~v5_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.69/2.17  tff(c_1809, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1736, c_1800])).
% 5.69/2.17  tff(c_1821, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1686, c_1809])).
% 5.69/2.17  tff(c_1825, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1821])).
% 5.69/2.17  tff(c_2081, plain, (![C_241, B_242, A_243]: (v2_funct_2(C_241, B_242) | ~v3_funct_2(C_241, A_243, B_242) | ~v1_funct_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_2093, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2081])).
% 5.69/2.17  tff(c_2103, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2093])).
% 5.69/2.17  tff(c_2105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1825, c_2103])).
% 5.69/2.17  tff(c_2106, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1821])).
% 5.69/2.17  tff(c_142, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_133, c_6])).
% 5.69/2.17  tff(c_1753, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1669, c_142])).
% 5.69/2.17  tff(c_1754, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1753])).
% 5.69/2.17  tff(c_2133, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_1754])).
% 5.69/2.17  tff(c_2225, plain, (![C_250, B_251, A_252]: (v2_funct_2(C_250, B_251) | ~v3_funct_2(C_250, A_252, B_251) | ~v1_funct_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.69/2.17  tff(c_2231, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_68, c_2225])).
% 5.69/2.17  tff(c_2235, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2231])).
% 5.69/2.17  tff(c_1735, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1724])).
% 5.69/2.17  tff(c_1812, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1735, c_1800])).
% 5.69/2.17  tff(c_1824, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_1812])).
% 5.69/2.17  tff(c_2263, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2235, c_1824])).
% 5.69/2.17  tff(c_2264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2133, c_2263])).
% 5.69/2.17  tff(c_2265, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1753])).
% 5.69/2.17  tff(c_8, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.17  tff(c_141, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_133, c_8])).
% 5.69/2.17  tff(c_1691, plain, (k1_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1669, c_141])).
% 5.69/2.17  tff(c_1692, plain, (k1_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1691])).
% 5.69/2.17  tff(c_2267, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2265, c_1692])).
% 5.69/2.17  tff(c_2279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1679, c_2267])).
% 5.69/2.17  tff(c_2280, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1691])).
% 5.69/2.17  tff(c_2281, plain, (k1_relat_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1691])).
% 5.69/2.17  tff(c_2300, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_2281])).
% 5.69/2.17  tff(c_2571, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_2540, c_2300])).
% 5.69/2.17  tff(c_89, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.69/2.17  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.69/2.17  tff(c_95, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89, c_10])).
% 5.69/2.17  tff(c_1677, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1669, c_95])).
% 5.69/2.17  tff(c_2567, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_2540, c_1677])).
% 5.69/2.17  tff(c_48, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.69/2.17  tff(c_12, plain, (![A_2, B_4]: (k2_funct_1(A_2)=B_4 | k6_relat_1(k2_relat_1(A_2))!=k5_relat_1(B_4, A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.69/2.17  tff(c_2815, plain, (![A_306, B_307]: (k2_funct_1(A_306)=B_307 | k6_partfun1(k2_relat_1(A_306))!=k5_relat_1(B_307, A_306) | k2_relat_1(B_307)!=k1_relat_1(A_306) | ~v2_funct_1(A_306) | ~v1_funct_1(B_307) | ~v1_relat_1(B_307) | ~v1_funct_1(A_306) | ~v1_relat_1(A_306))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 5.69/2.17  tff(c_2817, plain, (![B_307]: (k2_funct_1('#skF_1')=B_307 | k5_relat_1(B_307, '#skF_1')!=k6_partfun1('#skF_1') | k2_relat_1(B_307)!=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_307) | ~v1_relat_1(B_307) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2573, c_2815])).
% 5.69/2.17  tff(c_2826, plain, (![B_309]: (k2_funct_1('#skF_1')=B_309 | k5_relat_1(B_309, '#skF_1')!='#skF_1' | k2_relat_1(B_309)!='#skF_1' | ~v1_funct_1(B_309) | ~v1_relat_1(B_309))), inference(demodulation, [status(thm), theory('equality')], [c_2576, c_2580, c_2714, c_2571, c_2567, c_2817])).
% 5.69/2.17  tff(c_2829, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k2_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2576, c_2826])).
% 5.69/2.17  tff(c_2835, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2573, c_2829])).
% 5.69/2.17  tff(c_2837, plain, (k5_relat_1('#skF_1', '#skF_1')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2835])).
% 5.69/2.17  tff(c_2860, plain, (![C_318, A_321, F_320, E_322, D_323, B_319]: (k1_partfun1(A_321, B_319, C_318, D_323, E_322, F_320)=k5_relat_1(E_322, F_320) | ~m1_subset_1(F_320, k1_zfmisc_1(k2_zfmisc_1(C_318, D_323))) | ~v1_funct_1(F_320) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(A_321, B_319))) | ~v1_funct_1(E_322))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.69/2.17  tff(c_2862, plain, (![A_321, B_319, E_322]: (k1_partfun1(A_321, B_319, '#skF_1', '#skF_1', E_322, '#skF_1')=k5_relat_1(E_322, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(A_321, B_319))) | ~v1_funct_1(E_322))), inference(resolution, [status(thm)], [c_2577, c_2860])).
% 5.69/2.17  tff(c_2886, plain, (![A_328, B_329, E_330]: (k1_partfun1(A_328, B_329, '#skF_1', '#skF_1', E_330, '#skF_1')=k5_relat_1(E_330, '#skF_1') | ~m1_subset_1(E_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))) | ~v1_funct_1(E_330))), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2862])).
% 5.69/2.17  tff(c_2889, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2577, c_2886])).
% 5.69/2.17  tff(c_2895, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2889])).
% 5.69/2.17  tff(c_2284, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_58])).
% 5.69/2.17  tff(c_2563, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_2540, c_2284])).
% 5.69/2.17  tff(c_2771, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2567, c_2563])).
% 5.69/2.17  tff(c_24, plain, (![D_17, C_16, A_14, B_15]: (D_17=C_16 | ~r2_relset_1(A_14, B_15, C_16, D_17) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.69/2.17  tff(c_2773, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_2771, c_24])).
% 5.69/2.17  tff(c_2776, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2577, c_2773])).
% 5.69/2.17  tff(c_2850, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2776])).
% 5.69/2.17  tff(c_2898, plain, (~m1_subset_1(k5_relat_1('#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2895, c_2850])).
% 5.69/2.17  tff(c_2910, plain, (![C_331, D_335, B_334, A_336, F_332, E_333]: (m1_subset_1(k1_partfun1(A_336, B_334, C_331, D_335, E_333, F_332), k1_zfmisc_1(k2_zfmisc_1(A_336, D_335))) | ~m1_subset_1(F_332, k1_zfmisc_1(k2_zfmisc_1(C_331, D_335))) | ~v1_funct_1(F_332) | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_336, B_334))) | ~v1_funct_1(E_333))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.69/2.17  tff(c_2947, plain, (m1_subset_1(k5_relat_1('#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2895, c_2910])).
% 5.69/2.17  tff(c_2961, plain, (m1_subset_1(k5_relat_1('#skF_1', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2577, c_2580, c_2577, c_2947])).
% 5.69/2.17  tff(c_2963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2898, c_2961])).
% 5.69/2.17  tff(c_2964, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2776])).
% 5.69/2.17  tff(c_3025, plain, (![C_354, B_355, A_357, E_358, D_359, F_356]: (k1_partfun1(A_357, B_355, C_354, D_359, E_358, F_356)=k5_relat_1(E_358, F_356) | ~m1_subset_1(F_356, k1_zfmisc_1(k2_zfmisc_1(C_354, D_359))) | ~v1_funct_1(F_356) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_357, B_355))) | ~v1_funct_1(E_358))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.69/2.17  tff(c_3027, plain, (![A_357, B_355, E_358]: (k1_partfun1(A_357, B_355, '#skF_1', '#skF_1', E_358, '#skF_1')=k5_relat_1(E_358, '#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_357, B_355))) | ~v1_funct_1(E_358))), inference(resolution, [status(thm)], [c_2577, c_3025])).
% 5.69/2.17  tff(c_3085, plain, (![A_366, B_367, E_368]: (k1_partfun1(A_366, B_367, '#skF_1', '#skF_1', E_368, '#skF_1')=k5_relat_1(E_368, '#skF_1') | ~m1_subset_1(E_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))) | ~v1_funct_1(E_368))), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_3027])).
% 5.69/2.17  tff(c_3091, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')=k5_relat_1('#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2577, c_3085])).
% 5.69/2.17  tff(c_3098, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2964, c_3091])).
% 5.69/2.17  tff(c_3100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2837, c_3098])).
% 5.69/2.17  tff(c_3101, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2835])).
% 5.69/2.17  tff(c_2578, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_64])).
% 5.69/2.17  tff(c_2742, plain, (![A_299, B_300]: (k2_funct_2(A_299, B_300)=k2_funct_1(B_300) | ~m1_subset_1(B_300, k1_zfmisc_1(k2_zfmisc_1(A_299, A_299))) | ~v3_funct_2(B_300, A_299, A_299) | ~v1_funct_2(B_300, A_299, A_299) | ~v1_funct_1(B_300))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.69/2.17  tff(c_2745, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2577, c_2742])).
% 5.69/2.17  tff(c_2751, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2580, c_2578, c_2579, c_2745])).
% 5.69/2.17  tff(c_2285, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_56])).
% 5.69/2.17  tff(c_2566, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2540, c_2540, c_2285])).
% 5.69/2.17  tff(c_2753, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_2566])).
% 5.69/2.17  tff(c_3104, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3101, c_2753])).
% 5.69/2.17  tff(c_3108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2558, c_3104])).
% 5.69/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.17  
% 5.69/2.17  Inference rules
% 5.69/2.17  ----------------------
% 5.69/2.17  #Ref     : 0
% 5.69/2.17  #Sup     : 641
% 5.69/2.17  #Fact    : 0
% 5.69/2.17  #Define  : 0
% 5.69/2.17  #Split   : 26
% 5.69/2.17  #Chain   : 0
% 5.69/2.17  #Close   : 0
% 5.69/2.17  
% 5.69/2.17  Ordering : KBO
% 5.69/2.17  
% 5.69/2.17  Simplification rules
% 5.69/2.17  ----------------------
% 5.69/2.17  #Subsume      : 56
% 5.69/2.17  #Demod        : 838
% 5.69/2.17  #Tautology    : 301
% 5.69/2.17  #SimpNegUnit  : 15
% 5.69/2.17  #BackRed      : 105
% 5.69/2.17  
% 5.69/2.17  #Partial instantiations: 0
% 5.69/2.17  #Strategies tried      : 1
% 5.69/2.17  
% 5.69/2.17  Timing (in seconds)
% 5.69/2.17  ----------------------
% 5.69/2.17  Preprocessing        : 0.41
% 5.69/2.17  Parsing              : 0.23
% 5.69/2.17  CNF conversion       : 0.03
% 5.69/2.17  Main loop            : 0.87
% 5.69/2.17  Inferencing          : 0.30
% 5.69/2.17  Reduction            : 0.33
% 5.69/2.17  Demodulation         : 0.23
% 5.69/2.17  BG Simplification    : 0.04
% 5.69/2.17  Subsumption          : 0.13
% 5.69/2.17  Abstraction          : 0.04
% 5.69/2.17  MUC search           : 0.00
% 5.69/2.17  Cooper               : 0.00
% 5.69/2.17  Total                : 1.35
% 5.69/2.17  Index Insertion      : 0.00
% 5.69/2.17  Index Deletion       : 0.00
% 5.69/2.17  Index Matching       : 0.00
% 5.69/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
