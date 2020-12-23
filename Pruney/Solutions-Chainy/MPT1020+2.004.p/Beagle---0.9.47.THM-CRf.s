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
% DateTime   : Thu Dec  3 10:15:50 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  200 (9753 expanded)
%              Number of leaves         :   43 (3132 expanded)
%              Depth                    :   21
%              Number of atoms          :  345 (24465 expanded)
%              Number of equality atoms :   90 (3737 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_192,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_170,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_112,axiom,(
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

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_335,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_relset_1(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_348,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_335])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_276,plain,(
    ! [C_74,B_75,A_76] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(B_75,A_76)))
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_293,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_276])).

tff(c_297,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_76,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_74,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_120,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_135,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_120])).

tff(c_210,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_227,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_210])).

tff(c_411,plain,(
    ! [B_87,A_88] :
      ( k2_relat_1(B_87) = A_88
      | ~ v2_funct_2(B_87,A_88)
      | ~ v5_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_423,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_227,c_411])).

tff(c_435,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_423])).

tff(c_667,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_72,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_747,plain,(
    ! [C_127,B_128,A_129] :
      ( v2_funct_2(C_127,B_128)
      | ~ v3_funct_2(C_127,A_129,B_128)
      | ~ v1_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_753,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_747])).

tff(c_766,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_753])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_766])).

tff(c_769,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_781,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_787,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_781])).

tff(c_799,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_787])).

tff(c_831,plain,(
    ! [C_135,A_136,B_137] :
      ( v2_funct_1(C_135)
      | ~ v3_funct_2(C_135,A_136,B_137)
      | ~ v1_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_837,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_831])).

tff(c_850,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_837])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1858,plain,(
    ! [C_198,D_199,B_200,A_201] :
      ( k2_funct_1(C_198) = D_199
      | k1_xboole_0 = B_200
      | k1_xboole_0 = A_201
      | ~ v2_funct_1(C_198)
      | ~ r2_relset_1(A_201,A_201,k1_partfun1(A_201,B_200,B_200,A_201,C_198,D_199),k6_partfun1(A_201))
      | k2_relset_1(A_201,B_200,C_198) != B_200
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(B_200,A_201)))
      | ~ v1_funct_2(D_199,B_200,A_201)
      | ~ v1_funct_1(D_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200)))
      | ~ v1_funct_2(C_198,A_201,B_200)
      | ~ v1_funct_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1873,plain,
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
    inference(resolution,[status(thm)],[c_60,c_1858])).

tff(c_1878,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_62,c_799,c_850,c_1873])).

tff(c_1879,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1878])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1913,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_2])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_1913])).

tff(c_1916,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1878])).

tff(c_1052,plain,(
    ! [A_171,B_172] :
      ( k2_funct_2(A_171,B_172) = k2_funct_1(B_172)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(k2_zfmisc_1(A_171,A_171)))
      | ~ v3_funct_2(B_172,A_171,A_171)
      | ~ v1_funct_2(B_172,A_171,A_171)
      | ~ v1_funct_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1058,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1052])).

tff(c_1073,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1058])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1078,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_58])).

tff(c_1932,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1916,c_1078])).

tff(c_1951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_1932])).

tff(c_1953,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_100,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_1966,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1953,c_103])).

tff(c_1952,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_1959,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1952,c_103])).

tff(c_1987,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1966,c_1959])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1978,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1959,c_1959,c_8])).

tff(c_2067,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1987,c_1987,c_1978])).

tff(c_155,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_172,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_155])).

tff(c_197,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_2068,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2067,c_197])).

tff(c_2072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_2068])).

tff(c_2074,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_173,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_155])).

tff(c_2082,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_2128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_2082])).

tff(c_2130,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2129,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2136,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2129,c_103])).

tff(c_2073,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_2080,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2073,c_103])).

tff(c_2150,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_2080])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2081,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2073,c_4])).

tff(c_2221,plain,(
    ! [A_217] :
      ( A_217 = '#skF_3'
      | ~ v1_xboole_0(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2081])).

tff(c_2228,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2130,c_2221])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2139,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_2'
      | A_3 = '#skF_2'
      | k2_zfmisc_1(A_3,B_4) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_2080,c_6])).

tff(c_4312,plain,(
    ! [B_373,A_374] :
      ( B_373 = '#skF_3'
      | A_374 = '#skF_3'
      | k2_zfmisc_1(A_374,B_373) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2150,c_2150,c_2139])).

tff(c_4322,plain,(
    '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2228,c_4312])).

tff(c_2689,plain,(
    ! [B_257,A_258] :
      ( B_257 = '#skF_3'
      | A_258 = '#skF_3'
      | k2_zfmisc_1(A_258,B_257) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2150,c_2150,c_2139])).

tff(c_2699,plain,(
    '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2228,c_2689])).

tff(c_136,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_120])).

tff(c_2174,plain,(
    ! [C_209,B_210,A_211] :
      ( v5_relat_1(C_209,B_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2182,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_2174])).

tff(c_2410,plain,(
    ! [B_228,A_229] :
      ( k2_relat_1(B_228) = A_229
      | ~ v2_funct_2(B_228,A_229)
      | ~ v5_relat_1(B_228,A_229)
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2419,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2182,c_2410])).

tff(c_2428,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2419])).

tff(c_2429,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2428])).

tff(c_2718,plain,(
    ~ v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_2429])).

tff(c_2739,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_68])).

tff(c_110,plain,(
    ! [A_52] : m1_subset_1(k6_partfun1(A_52),k1_zfmisc_1(k2_zfmisc_1(A_52,A_52))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_114,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_110])).

tff(c_158,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_114,c_155])).

tff(c_170,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_158])).

tff(c_179,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_103])).

tff(c_2138,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_179])).

tff(c_2183,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2150,c_2138])).

tff(c_2732,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_2699,c_2183])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2738,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2699,c_64])).

tff(c_48,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2748,plain,(
    ! [C_259,B_260,A_261] :
      ( v2_funct_2(C_259,B_260)
      | ~ v3_funct_2(C_259,A_261,B_260)
      | ~ v1_funct_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_261,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4011,plain,(
    ! [A_343] :
      ( v2_funct_2(k6_partfun1(A_343),A_343)
      | ~ v3_funct_2(k6_partfun1(A_343),A_343,A_343)
      | ~ v1_funct_1(k6_partfun1(A_343)) ) ),
    inference(resolution,[status(thm)],[c_48,c_2748])).

tff(c_4023,plain,
    ( v2_funct_2(k6_partfun1('#skF_1'),'#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2732,c_4011])).

tff(c_4025,plain,(
    v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_2732,c_2738,c_2732,c_4023])).

tff(c_4027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2718,c_4025])).

tff(c_4029,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2428])).

tff(c_4340,plain,(
    v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4322,c_4029])).

tff(c_4028,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2428])).

tff(c_2203,plain,(
    ! [A_212] : v5_relat_1(k6_partfun1(A_212),A_212) ),
    inference(resolution,[status(thm)],[c_48,c_2174])).

tff(c_2206,plain,(
    v5_relat_1('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2183,c_2203])).

tff(c_2413,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_2('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2206,c_2410])).

tff(c_2422,plain,
    ( k2_relat_1('#skF_3') = '#skF_3'
    | ~ v2_funct_2('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_2413])).

tff(c_4086,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4028,c_2422])).

tff(c_4087,plain,(
    ~ v2_funct_2('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4086])).

tff(c_4338,plain,(
    ~ v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4322,c_4322,c_4087])).

tff(c_4458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4340,c_4338])).

tff(c_4459,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4086])).

tff(c_2142,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_8])).

tff(c_2254,plain,(
    ! [A_219] : k2_zfmisc_1(A_219,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2150,c_2142])).

tff(c_2271,plain,(
    m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2254,c_48])).

tff(c_2279,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_2271])).

tff(c_4478,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4459,c_2279])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2143,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_10])).

tff(c_2232,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2150,c_2143])).

tff(c_4575,plain,(
    ! [B_391] : k2_zfmisc_1('#skF_1',B_391) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4459,c_2232])).

tff(c_24,plain,(
    ! [A_21,B_22,D_24] :
      ( r2_relset_1(A_21,B_22,D_24,D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4990,plain,(
    ! [B_441,D_442] :
      ( r2_relset_1('#skF_1',B_441,D_442,D_442)
      | ~ m1_subset_1(D_442,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4575,c_24])).

tff(c_4993,plain,(
    ! [B_441] : r2_relset_1('#skF_1',B_441,'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_4478,c_4990])).

tff(c_4495,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_68])).

tff(c_4493,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_66])).

tff(c_4494,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_64])).

tff(c_2253,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2150,c_2142])).

tff(c_4479,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4459,c_2253])).

tff(c_4487,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4459,c_2183])).

tff(c_4896,plain,(
    ! [A_426,B_427] :
      ( k2_funct_2(A_426,B_427) = k2_funct_1(B_427)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(k2_zfmisc_1(A_426,A_426)))
      | ~ v3_funct_2(B_427,A_426,A_426)
      | ~ v1_funct_2(B_427,A_426,A_426)
      | ~ v1_funct_1(B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_9039,plain,(
    ! [A_534] :
      ( k2_funct_2(A_534,k6_partfun1(A_534)) = k2_funct_1(k6_partfun1(A_534))
      | ~ v3_funct_2(k6_partfun1(A_534),A_534,A_534)
      | ~ v1_funct_2(k6_partfun1(A_534),A_534,A_534)
      | ~ v1_funct_1(k6_partfun1(A_534)) ) ),
    inference(resolution,[status(thm)],[c_48,c_4896])).

tff(c_9063,plain,
    ( k2_funct_2('#skF_1',k6_partfun1('#skF_1')) = k2_funct_1(k6_partfun1('#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2(k6_partfun1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4487,c_9039])).

tff(c_9065,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4495,c_4487,c_4493,c_4487,c_4494,c_4487,c_4487,c_9063])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k2_funct_2(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9073,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9065,c_38])).

tff(c_9077,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4495,c_4493,c_4494,c_4478,c_4479,c_4479,c_9073])).

tff(c_2352,plain,(
    ! [C_221,B_222,A_223] :
      ( v1_xboole_0(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(B_222,A_223)))
      | ~ v1_xboole_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2358,plain,(
    ! [C_221] :
      ( v1_xboole_0(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2253,c_2352])).

tff(c_2366,plain,(
    ! [C_221] :
      ( v1_xboole_0(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2358])).

tff(c_4471,plain,(
    ! [C_221] :
      ( v1_xboole_0(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_2366])).

tff(c_9117,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9077,c_4471])).

tff(c_2220,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2081])).

tff(c_4481,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_2220])).

tff(c_9151,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_9117,c_4481])).

tff(c_2158,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_58])).

tff(c_4485,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4459,c_2158])).

tff(c_9069,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9065,c_4485])).

tff(c_9157,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9151,c_9069])).

tff(c_9166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4993,c_9157])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.35/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.71  
% 7.45/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.45/2.71  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.45/2.71  
% 7.45/2.71  %Foreground sorts:
% 7.45/2.71  
% 7.45/2.71  
% 7.45/2.71  %Background operators:
% 7.45/2.71  
% 7.45/2.71  
% 7.45/2.71  %Foreground operators:
% 7.45/2.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.45/2.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.45/2.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.45/2.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.45/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.71  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.45/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.45/2.71  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 7.45/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.45/2.71  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.45/2.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.45/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.45/2.71  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.45/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.45/2.71  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.45/2.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.45/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.71  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.45/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.45/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.45/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.45/2.71  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.45/2.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.45/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.71  
% 7.64/2.75  tff(f_192, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 7.64/2.75  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.64/2.75  tff(f_64, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.64/2.75  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.64/2.75  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.64/2.75  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.64/2.75  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.64/2.75  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.64/2.75  tff(f_170, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.64/2.75  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.64/2.75  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 7.64/2.75  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.64/2.75  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.64/2.75  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.64/2.75  tff(f_116, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.64/2.75  tff(f_112, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 7.64/2.75  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_335, plain, (![A_81, B_82, D_83]: (r2_relset_1(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.64/2.75  tff(c_348, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_335])).
% 7.64/2.75  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_276, plain, (![C_74, B_75, A_76]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(B_75, A_76))) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.64/2.75  tff(c_293, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_276])).
% 7.64/2.75  tff(c_297, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_293])).
% 7.64/2.75  tff(c_76, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_74, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_120, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.64/2.75  tff(c_135, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_120])).
% 7.64/2.75  tff(c_210, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.64/2.75  tff(c_227, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_210])).
% 7.64/2.75  tff(c_411, plain, (![B_87, A_88]: (k2_relat_1(B_87)=A_88 | ~v2_funct_2(B_87, A_88) | ~v5_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.64/2.75  tff(c_423, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_227, c_411])).
% 7.64/2.75  tff(c_435, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_423])).
% 7.64/2.75  tff(c_667, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_435])).
% 7.64/2.75  tff(c_72, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_747, plain, (![C_127, B_128, A_129]: (v2_funct_2(C_127, B_128) | ~v3_funct_2(C_127, A_129, B_128) | ~v1_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.64/2.75  tff(c_753, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_747])).
% 7.64/2.75  tff(c_766, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_753])).
% 7.64/2.75  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_667, c_766])).
% 7.64/2.75  tff(c_769, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_435])).
% 7.64/2.75  tff(c_781, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.64/2.75  tff(c_787, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_781])).
% 7.64/2.75  tff(c_799, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_769, c_787])).
% 7.64/2.75  tff(c_831, plain, (![C_135, A_136, B_137]: (v2_funct_1(C_135) | ~v3_funct_2(C_135, A_136, B_137) | ~v1_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.64/2.75  tff(c_837, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_831])).
% 7.64/2.75  tff(c_850, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_837])).
% 7.64/2.75  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_1858, plain, (![C_198, D_199, B_200, A_201]: (k2_funct_1(C_198)=D_199 | k1_xboole_0=B_200 | k1_xboole_0=A_201 | ~v2_funct_1(C_198) | ~r2_relset_1(A_201, A_201, k1_partfun1(A_201, B_200, B_200, A_201, C_198, D_199), k6_partfun1(A_201)) | k2_relset_1(A_201, B_200, C_198)!=B_200 | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(B_200, A_201))) | ~v1_funct_2(D_199, B_200, A_201) | ~v1_funct_1(D_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))) | ~v1_funct_2(C_198, A_201, B_200) | ~v1_funct_1(C_198))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.64/2.75  tff(c_1873, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1858])).
% 7.64/2.75  tff(c_1878, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_62, c_799, c_850, c_1873])).
% 7.64/2.75  tff(c_1879, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1878])).
% 7.64/2.75  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.64/2.75  tff(c_1913, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1879, c_2])).
% 7.64/2.75  tff(c_1915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_1913])).
% 7.64/2.75  tff(c_1916, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1878])).
% 7.64/2.75  tff(c_1052, plain, (![A_171, B_172]: (k2_funct_2(A_171, B_172)=k2_funct_1(B_172) | ~m1_subset_1(B_172, k1_zfmisc_1(k2_zfmisc_1(A_171, A_171))) | ~v3_funct_2(B_172, A_171, A_171) | ~v1_funct_2(B_172, A_171, A_171) | ~v1_funct_1(B_172))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.75  tff(c_1058, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1052])).
% 7.64/2.75  tff(c_1073, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1058])).
% 7.64/2.75  tff(c_58, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_1078, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_58])).
% 7.64/2.75  tff(c_1932, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1916, c_1078])).
% 7.64/2.75  tff(c_1951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_1932])).
% 7.64/2.75  tff(c_1953, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_293])).
% 7.64/2.75  tff(c_100, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.64/2.75  tff(c_103, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_2, c_100])).
% 7.64/2.75  tff(c_1966, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1953, c_103])).
% 7.64/2.75  tff(c_1952, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_293])).
% 7.64/2.75  tff(c_1959, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1952, c_103])).
% 7.64/2.75  tff(c_1987, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1966, c_1959])).
% 7.64/2.75  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.64/2.75  tff(c_1978, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1959, c_1959, c_8])).
% 7.64/2.75  tff(c_2067, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1987, c_1987, c_1978])).
% 7.64/2.75  tff(c_155, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.64/2.75  tff(c_172, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_155])).
% 7.64/2.75  tff(c_197, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitLeft, [status(thm)], [c_172])).
% 7.64/2.75  tff(c_2068, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2067, c_197])).
% 7.64/2.75  tff(c_2072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1953, c_2068])).
% 7.64/2.75  tff(c_2074, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_172])).
% 7.64/2.75  tff(c_173, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_155])).
% 7.64/2.75  tff(c_2082, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitLeft, [status(thm)], [c_173])).
% 7.64/2.75  tff(c_2128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2074, c_2082])).
% 7.64/2.75  tff(c_2130, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_173])).
% 7.64/2.75  tff(c_2129, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_173])).
% 7.64/2.75  tff(c_2136, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2129, c_103])).
% 7.64/2.75  tff(c_2073, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 7.64/2.75  tff(c_2080, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2073, c_103])).
% 7.64/2.75  tff(c_2150, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_2080])).
% 7.64/2.75  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.64/2.75  tff(c_2081, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2073, c_4])).
% 7.64/2.75  tff(c_2221, plain, (![A_217]: (A_217='#skF_3' | ~v1_xboole_0(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2081])).
% 7.64/2.75  tff(c_2228, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_2130, c_2221])).
% 7.64/2.75  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.64/2.75  tff(c_2139, plain, (![B_4, A_3]: (B_4='#skF_2' | A_3='#skF_2' | k2_zfmisc_1(A_3, B_4)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_2080, c_6])).
% 7.64/2.75  tff(c_4312, plain, (![B_373, A_374]: (B_373='#skF_3' | A_374='#skF_3' | k2_zfmisc_1(A_374, B_373)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2150, c_2150, c_2139])).
% 7.64/2.75  tff(c_4322, plain, ('#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2228, c_4312])).
% 7.64/2.75  tff(c_2689, plain, (![B_257, A_258]: (B_257='#skF_3' | A_258='#skF_3' | k2_zfmisc_1(A_258, B_257)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2150, c_2150, c_2139])).
% 7.64/2.75  tff(c_2699, plain, ('#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2228, c_2689])).
% 7.64/2.75  tff(c_136, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_120])).
% 7.64/2.75  tff(c_2174, plain, (![C_209, B_210, A_211]: (v5_relat_1(C_209, B_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.64/2.75  tff(c_2182, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_2174])).
% 7.64/2.75  tff(c_2410, plain, (![B_228, A_229]: (k2_relat_1(B_228)=A_229 | ~v2_funct_2(B_228, A_229) | ~v5_relat_1(B_228, A_229) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.64/2.75  tff(c_2419, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2182, c_2410])).
% 7.64/2.75  tff(c_2428, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2419])).
% 7.64/2.75  tff(c_2429, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_2428])).
% 7.64/2.75  tff(c_2718, plain, (~v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_2429])).
% 7.64/2.75  tff(c_2739, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_68])).
% 7.64/2.75  tff(c_110, plain, (![A_52]: (m1_subset_1(k6_partfun1(A_52), k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.64/2.75  tff(c_114, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_110])).
% 7.64/2.75  tff(c_158, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_155])).
% 7.64/2.75  tff(c_170, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_158])).
% 7.64/2.75  tff(c_179, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_103])).
% 7.64/2.75  tff(c_2138, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_179])).
% 7.64/2.75  tff(c_2183, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2150, c_2138])).
% 7.64/2.75  tff(c_2732, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_2699, c_2183])).
% 7.64/2.75  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.64/2.75  tff(c_2738, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2699, c_64])).
% 7.64/2.75  tff(c_48, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.64/2.75  tff(c_2748, plain, (![C_259, B_260, A_261]: (v2_funct_2(C_259, B_260) | ~v3_funct_2(C_259, A_261, B_260) | ~v1_funct_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_261, B_260))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.64/2.75  tff(c_4011, plain, (![A_343]: (v2_funct_2(k6_partfun1(A_343), A_343) | ~v3_funct_2(k6_partfun1(A_343), A_343, A_343) | ~v1_funct_1(k6_partfun1(A_343)))), inference(resolution, [status(thm)], [c_48, c_2748])).
% 7.64/2.75  tff(c_4023, plain, (v2_funct_2(k6_partfun1('#skF_1'), '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2732, c_4011])).
% 7.64/2.75  tff(c_4025, plain, (v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2739, c_2732, c_2738, c_2732, c_4023])).
% 7.64/2.75  tff(c_4027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2718, c_4025])).
% 7.64/2.75  tff(c_4029, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_2428])).
% 7.64/2.75  tff(c_4340, plain, (v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4322, c_4029])).
% 7.64/2.75  tff(c_4028, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2428])).
% 7.64/2.75  tff(c_2203, plain, (![A_212]: (v5_relat_1(k6_partfun1(A_212), A_212))), inference(resolution, [status(thm)], [c_48, c_2174])).
% 7.64/2.75  tff(c_2206, plain, (v5_relat_1('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2183, c_2203])).
% 7.64/2.75  tff(c_2413, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_2('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2206, c_2410])).
% 7.64/2.75  tff(c_2422, plain, (k2_relat_1('#skF_3')='#skF_3' | ~v2_funct_2('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_2413])).
% 7.64/2.75  tff(c_4086, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4028, c_2422])).
% 7.64/2.75  tff(c_4087, plain, (~v2_funct_2('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_4086])).
% 7.64/2.75  tff(c_4338, plain, (~v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4322, c_4322, c_4087])).
% 7.64/2.75  tff(c_4458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4340, c_4338])).
% 7.64/2.75  tff(c_4459, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_4086])).
% 7.64/2.75  tff(c_2142, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_8])).
% 7.64/2.75  tff(c_2254, plain, (![A_219]: (k2_zfmisc_1(A_219, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2150, c_2142])).
% 7.64/2.75  tff(c_2271, plain, (m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2254, c_48])).
% 7.64/2.75  tff(c_2279, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_2271])).
% 7.64/2.75  tff(c_4478, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4459, c_2279])).
% 7.64/2.75  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.64/2.75  tff(c_2143, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_10])).
% 7.64/2.75  tff(c_2232, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2150, c_2143])).
% 7.64/2.75  tff(c_4575, plain, (![B_391]: (k2_zfmisc_1('#skF_1', B_391)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4459, c_2232])).
% 7.64/2.75  tff(c_24, plain, (![A_21, B_22, D_24]: (r2_relset_1(A_21, B_22, D_24, D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.64/2.75  tff(c_4990, plain, (![B_441, D_442]: (r2_relset_1('#skF_1', B_441, D_442, D_442) | ~m1_subset_1(D_442, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4575, c_24])).
% 7.64/2.75  tff(c_4993, plain, (![B_441]: (r2_relset_1('#skF_1', B_441, '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_4478, c_4990])).
% 7.64/2.75  tff(c_4495, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_68])).
% 7.64/2.75  tff(c_4493, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_66])).
% 7.64/2.75  tff(c_4494, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_64])).
% 7.64/2.75  tff(c_2253, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2150, c_2142])).
% 7.64/2.75  tff(c_4479, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4459, c_2253])).
% 7.64/2.75  tff(c_4487, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4459, c_2183])).
% 7.64/2.75  tff(c_4896, plain, (![A_426, B_427]: (k2_funct_2(A_426, B_427)=k2_funct_1(B_427) | ~m1_subset_1(B_427, k1_zfmisc_1(k2_zfmisc_1(A_426, A_426))) | ~v3_funct_2(B_427, A_426, A_426) | ~v1_funct_2(B_427, A_426, A_426) | ~v1_funct_1(B_427))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.64/2.75  tff(c_9039, plain, (![A_534]: (k2_funct_2(A_534, k6_partfun1(A_534))=k2_funct_1(k6_partfun1(A_534)) | ~v3_funct_2(k6_partfun1(A_534), A_534, A_534) | ~v1_funct_2(k6_partfun1(A_534), A_534, A_534) | ~v1_funct_1(k6_partfun1(A_534)))), inference(resolution, [status(thm)], [c_48, c_4896])).
% 7.64/2.75  tff(c_9063, plain, (k2_funct_2('#skF_1', k6_partfun1('#skF_1'))=k2_funct_1(k6_partfun1('#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2(k6_partfun1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4487, c_9039])).
% 7.64/2.75  tff(c_9065, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4495, c_4487, c_4493, c_4487, c_4494, c_4487, c_4487, c_9063])).
% 7.64/2.75  tff(c_38, plain, (![A_30, B_31]: (m1_subset_1(k2_funct_2(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.64/2.75  tff(c_9073, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9065, c_38])).
% 7.64/2.75  tff(c_9077, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4495, c_4493, c_4494, c_4478, c_4479, c_4479, c_9073])).
% 7.64/2.75  tff(c_2352, plain, (![C_221, B_222, A_223]: (v1_xboole_0(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(B_222, A_223))) | ~v1_xboole_0(A_223))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.64/2.75  tff(c_2358, plain, (![C_221]: (v1_xboole_0(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2253, c_2352])).
% 7.64/2.75  tff(c_2366, plain, (![C_221]: (v1_xboole_0(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2358])).
% 7.64/2.75  tff(c_4471, plain, (![C_221]: (v1_xboole_0(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_2366])).
% 7.64/2.75  tff(c_9117, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_9077, c_4471])).
% 7.64/2.75  tff(c_2220, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2081])).
% 7.64/2.75  tff(c_4481, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_2220])).
% 7.64/2.75  tff(c_9151, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_9117, c_4481])).
% 7.64/2.75  tff(c_2158, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_58])).
% 7.64/2.75  tff(c_4485, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4459, c_2158])).
% 7.64/2.75  tff(c_9069, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9065, c_4485])).
% 7.64/2.75  tff(c_9157, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9151, c_9069])).
% 7.64/2.75  tff(c_9166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4993, c_9157])).
% 7.64/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/2.75  
% 7.64/2.75  Inference rules
% 7.64/2.75  ----------------------
% 7.64/2.75  #Ref     : 0
% 7.64/2.75  #Sup     : 2323
% 7.64/2.75  #Fact    : 0
% 7.64/2.75  #Define  : 0
% 7.64/2.75  #Split   : 18
% 7.64/2.75  #Chain   : 0
% 7.64/2.75  #Close   : 0
% 7.64/2.75  
% 7.64/2.75  Ordering : KBO
% 7.64/2.75  
% 7.64/2.75  Simplification rules
% 7.64/2.75  ----------------------
% 7.64/2.75  #Subsume      : 476
% 7.64/2.75  #Demod        : 1954
% 7.64/2.75  #Tautology    : 841
% 7.64/2.75  #SimpNegUnit  : 5
% 7.64/2.75  #BackRed      : 226
% 7.64/2.75  
% 7.64/2.75  #Partial instantiations: 0
% 7.64/2.75  #Strategies tried      : 1
% 7.64/2.75  
% 7.64/2.75  Timing (in seconds)
% 7.64/2.75  ----------------------
% 7.64/2.75  Preprocessing        : 0.34
% 7.64/2.75  Parsing              : 0.18
% 7.64/2.75  CNF conversion       : 0.03
% 7.64/2.75  Main loop            : 1.52
% 7.64/2.75  Inferencing          : 0.47
% 7.64/2.76  Reduction            : 0.53
% 7.64/2.76  Demodulation         : 0.39
% 7.64/2.76  BG Simplification    : 0.06
% 7.64/2.76  Subsumption          : 0.32
% 7.64/2.76  Abstraction          : 0.06
% 7.64/2.76  MUC search           : 0.00
% 7.64/2.76  Cooper               : 0.00
% 7.64/2.76  Total                : 1.93
% 7.64/2.76  Index Insertion      : 0.00
% 7.64/2.76  Index Deletion       : 0.00
% 7.64/2.76  Index Matching       : 0.00
% 7.64/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
