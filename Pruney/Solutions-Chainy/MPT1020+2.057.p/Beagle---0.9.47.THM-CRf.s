%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:59 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  141 (1142 expanded)
%              Number of leaves         :   43 ( 392 expanded)
%              Depth                    :   15
%              Number of atoms          :  238 (3201 expanded)
%              Number of equality atoms :   57 ( 298 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_148,axiom,(
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

tff(f_102,axiom,(
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

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_54,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_304,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_relset_1(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_309,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_304])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_119,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_119])).

tff(c_131,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_125])).

tff(c_141,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_149,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_141])).

tff(c_151,plain,(
    ! [B_56,A_57] :
      ( k2_relat_1(B_56) = A_57
      | ~ v2_funct_2(B_56,A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_154,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_149,c_151])).

tff(c_160,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_154])).

tff(c_164,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_64,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_60,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_271,plain,(
    ! [C_79,B_80,A_81] :
      ( v2_funct_2(C_79,B_80)
      | ~ v3_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_277,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_271])).

tff(c_283,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_277])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_283])).

tff(c_286,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_294,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_10])).

tff(c_300,plain,
    ( ~ v1_xboole_0('#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_294])).

tff(c_303,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_62,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_372,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_378,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_372])).

tff(c_382,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_378])).

tff(c_391,plain,(
    ! [C_97,A_98,B_99] :
      ( v2_funct_1(C_97)
      | ~ v3_funct_2(C_97,A_98,B_99)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_397,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_391])).

tff(c_403,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_397])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_478,plain,(
    ! [C_123,D_124,B_125,A_126] :
      ( k2_funct_1(C_123) = D_124
      | k1_xboole_0 = B_125
      | k1_xboole_0 = A_126
      | ~ v2_funct_1(C_123)
      | ~ r2_relset_1(A_126,A_126,k1_partfun1(A_126,B_125,B_125,A_126,C_123,D_124),k6_partfun1(A_126))
      | k2_relset_1(A_126,B_125,C_123) != B_125
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(B_125,A_126)))
      | ~ v1_funct_2(D_124,B_125,A_126)
      | ~ v1_funct_1(D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125)))
      | ~ v1_funct_2(C_123,A_126,B_125)
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_481,plain,
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
    inference(resolution,[status(thm)],[c_48,c_478])).

tff(c_487,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_50,c_382,c_403,c_481])).

tff(c_489,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_497,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_2])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_497])).

tff(c_500,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_433,plain,(
    ! [A_107,B_108] :
      ( k2_funct_2(A_107,B_108) = k2_funct_1(B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ v3_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_439,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_433])).

tff(c_445,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_439])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_451,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_46])).

tff(c_502,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_451])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_502])).

tff(c_508,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_108,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_111,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_108])).

tff(c_521,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_508,c_111])).

tff(c_507,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_507,c_111])).

tff(c_540,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_514])).

tff(c_533,plain,(
    ! [A_127,B_128,D_129] :
      ( r2_relset_1(A_127,B_128,D_129,D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_539,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_533])).

tff(c_618,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_540,c_539])).

tff(c_556,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_64])).

tff(c_555,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_62])).

tff(c_554,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_60])).

tff(c_71,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_38,plain,(
    ! [A_27] : k6_relat_1(A_27) = k6_partfun1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_9] : k2_funct_1(k6_relat_1(A_9)) = k6_relat_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    ! [A_42] : k2_funct_1(k6_partfun1(A_42)) = k6_partfun1(A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_14])).

tff(c_100,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_91])).

tff(c_103,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_100])).

tff(c_524,plain,(
    k2_funct_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_514,c_103])).

tff(c_571,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_540,c_524])).

tff(c_553,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_58])).

tff(c_754,plain,(
    ! [A_147,B_148] :
      ( k2_funct_2(A_147,B_148) = k2_funct_1(B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_zfmisc_1(A_147,A_147)))
      | ~ v3_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_757,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_553,c_754])).

tff(c_760,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_555,c_554,c_571,c_757])).

tff(c_122,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_148,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_141])).

tff(c_157,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_151])).

tff(c_163,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_157])).

tff(c_658,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_661,plain,(
    ! [C_137,B_138,A_139] :
      ( v2_funct_2(C_137,B_138)
      | ~ v3_funct_2(C_137,A_139,B_138)
      | ~ v1_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_667,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_661])).

tff(c_673,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_667])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_673])).

tff(c_676,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_685,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_10])).

tff(c_691,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_508,c_685])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_522,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_508,c_4])).

tff(c_698,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_691,c_522])).

tff(c_552,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_46])).

tff(c_726,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_552])).

tff(c_761,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_726])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.48  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.48  
% 3.15/1.48  %Foreground sorts:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Background operators:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Foreground operators:
% 3.15/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.15/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.15/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.15/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.48  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.15/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.48  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.15/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.15/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.15/1.48  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.15/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.48  
% 3.33/1.50  tff(f_170, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 3.33/1.50  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.33/1.50  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.33/1.50  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.33/1.50  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.50  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 3.33/1.50  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.33/1.50  tff(f_51, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.33/1.50  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.33/1.50  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.33/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.33/1.50  tff(f_102, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.33/1.50  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.33/1.50  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.33/1.50  tff(f_52, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.33/1.50  tff(f_54, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.33/1.50  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_304, plain, (![A_82, B_83, D_84]: (r2_relset_1(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.33/1.50  tff(c_309, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_304])).
% 3.33/1.50  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.33/1.50  tff(c_58, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_119, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.50  tff(c_125, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_119])).
% 3.33/1.50  tff(c_131, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_125])).
% 3.33/1.50  tff(c_141, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.33/1.50  tff(c_149, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_141])).
% 3.33/1.50  tff(c_151, plain, (![B_56, A_57]: (k2_relat_1(B_56)=A_57 | ~v2_funct_2(B_56, A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.33/1.50  tff(c_154, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_149, c_151])).
% 3.33/1.50  tff(c_160, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_154])).
% 3.33/1.50  tff(c_164, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_160])).
% 3.33/1.50  tff(c_64, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_60, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_271, plain, (![C_79, B_80, A_81]: (v2_funct_2(C_79, B_80) | ~v3_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.33/1.50  tff(c_277, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_271])).
% 3.33/1.50  tff(c_283, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_277])).
% 3.33/1.50  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_283])).
% 3.33/1.50  tff(c_286, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_160])).
% 3.33/1.50  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k2_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.33/1.50  tff(c_294, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_286, c_10])).
% 3.33/1.50  tff(c_300, plain, (~v1_xboole_0('#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_294])).
% 3.33/1.50  tff(c_303, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_300])).
% 3.33/1.50  tff(c_62, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_372, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.33/1.50  tff(c_378, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_372])).
% 3.33/1.50  tff(c_382, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_378])).
% 3.33/1.50  tff(c_391, plain, (![C_97, A_98, B_99]: (v2_funct_1(C_97) | ~v3_funct_2(C_97, A_98, B_99) | ~v1_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.33/1.50  tff(c_397, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_391])).
% 3.33/1.50  tff(c_403, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_397])).
% 3.33/1.50  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_478, plain, (![C_123, D_124, B_125, A_126]: (k2_funct_1(C_123)=D_124 | k1_xboole_0=B_125 | k1_xboole_0=A_126 | ~v2_funct_1(C_123) | ~r2_relset_1(A_126, A_126, k1_partfun1(A_126, B_125, B_125, A_126, C_123, D_124), k6_partfun1(A_126)) | k2_relset_1(A_126, B_125, C_123)!=B_125 | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(B_125, A_126))) | ~v1_funct_2(D_124, B_125, A_126) | ~v1_funct_1(D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))) | ~v1_funct_2(C_123, A_126, B_125) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.33/1.50  tff(c_481, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_48, c_478])).
% 3.33/1.50  tff(c_487, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_50, c_382, c_403, c_481])).
% 3.33/1.50  tff(c_489, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_487])).
% 3.33/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.33/1.50  tff(c_497, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_2])).
% 3.33/1.50  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_497])).
% 3.33/1.50  tff(c_500, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_487])).
% 3.33/1.50  tff(c_433, plain, (![A_107, B_108]: (k2_funct_2(A_107, B_108)=k2_funct_1(B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~v3_funct_2(B_108, A_107, A_107) | ~v1_funct_2(B_108, A_107, A_107) | ~v1_funct_1(B_108))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.33/1.50  tff(c_439, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_58, c_433])).
% 3.33/1.50  tff(c_445, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_439])).
% 3.33/1.50  tff(c_46, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_451, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_46])).
% 3.33/1.50  tff(c_502, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_451])).
% 3.33/1.50  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_309, c_502])).
% 3.33/1.50  tff(c_508, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_300])).
% 3.33/1.50  tff(c_108, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | B_43=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.50  tff(c_111, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_2, c_108])).
% 3.33/1.50  tff(c_521, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_508, c_111])).
% 3.33/1.50  tff(c_507, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_300])).
% 3.33/1.50  tff(c_514, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_507, c_111])).
% 3.33/1.50  tff(c_540, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_521, c_514])).
% 3.33/1.50  tff(c_533, plain, (![A_127, B_128, D_129]: (r2_relset_1(A_127, B_128, D_129, D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.33/1.50  tff(c_539, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_533])).
% 3.33/1.50  tff(c_618, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_540, c_539])).
% 3.33/1.50  tff(c_556, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_64])).
% 3.33/1.50  tff(c_555, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_62])).
% 3.33/1.50  tff(c_554, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_60])).
% 3.33/1.50  tff(c_71, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.33/1.50  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.33/1.50  tff(c_77, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_71, c_12])).
% 3.33/1.50  tff(c_38, plain, (![A_27]: (k6_relat_1(A_27)=k6_partfun1(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.33/1.50  tff(c_14, plain, (![A_9]: (k2_funct_1(k6_relat_1(A_9))=k6_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.50  tff(c_91, plain, (![A_42]: (k2_funct_1(k6_partfun1(A_42))=k6_partfun1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_14])).
% 3.33/1.50  tff(c_100, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77, c_91])).
% 3.33/1.50  tff(c_103, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_100])).
% 3.33/1.50  tff(c_524, plain, (k2_funct_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_514, c_103])).
% 3.33/1.50  tff(c_571, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_540, c_524])).
% 3.33/1.50  tff(c_553, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_58])).
% 3.33/1.50  tff(c_754, plain, (![A_147, B_148]: (k2_funct_2(A_147, B_148)=k2_funct_1(B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_zfmisc_1(A_147, A_147))) | ~v3_funct_2(B_148, A_147, A_147) | ~v1_funct_2(B_148, A_147, A_147) | ~v1_funct_1(B_148))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.33/1.50  tff(c_757, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_553, c_754])).
% 3.33/1.50  tff(c_760, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_556, c_555, c_554, c_571, c_757])).
% 3.33/1.50  tff(c_122, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_119])).
% 3.33/1.50  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_122])).
% 3.33/1.50  tff(c_148, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_141])).
% 3.33/1.50  tff(c_157, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_151])).
% 3.33/1.50  tff(c_163, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_157])).
% 3.33/1.50  tff(c_658, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_163])).
% 3.33/1.50  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.33/1.50  tff(c_661, plain, (![C_137, B_138, A_139]: (v2_funct_2(C_137, B_138) | ~v3_funct_2(C_137, A_139, B_138) | ~v1_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.33/1.50  tff(c_667, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_661])).
% 3.33/1.50  tff(c_673, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_667])).
% 3.33/1.50  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_673])).
% 3.33/1.50  tff(c_676, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_163])).
% 3.33/1.50  tff(c_685, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_676, c_10])).
% 3.33/1.50  tff(c_691, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_508, c_685])).
% 3.33/1.50  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.33/1.50  tff(c_522, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_508, c_4])).
% 3.33/1.50  tff(c_698, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_691, c_522])).
% 3.33/1.50  tff(c_552, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_46])).
% 3.33/1.50  tff(c_726, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_698, c_552])).
% 3.33/1.50  tff(c_761, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_726])).
% 3.33/1.50  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_618, c_761])).
% 3.33/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.50  
% 3.33/1.50  Inference rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Ref     : 0
% 3.33/1.50  #Sup     : 145
% 3.33/1.50  #Fact    : 0
% 3.33/1.50  #Define  : 0
% 3.33/1.50  #Split   : 9
% 3.33/1.50  #Chain   : 0
% 3.33/1.50  #Close   : 0
% 3.33/1.50  
% 3.33/1.50  Ordering : KBO
% 3.33/1.50  
% 3.33/1.50  Simplification rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Subsume      : 4
% 3.33/1.50  #Demod        : 235
% 3.33/1.50  #Tautology    : 100
% 3.33/1.50  #SimpNegUnit  : 5
% 3.33/1.50  #BackRed      : 42
% 3.33/1.50  
% 3.33/1.50  #Partial instantiations: 0
% 3.33/1.50  #Strategies tried      : 1
% 3.33/1.50  
% 3.33/1.50  Timing (in seconds)
% 3.33/1.50  ----------------------
% 3.33/1.51  Preprocessing        : 0.35
% 3.33/1.51  Parsing              : 0.19
% 3.33/1.51  CNF conversion       : 0.02
% 3.33/1.51  Main loop            : 0.35
% 3.33/1.51  Inferencing          : 0.12
% 3.33/1.51  Reduction            : 0.13
% 3.33/1.51  Demodulation         : 0.09
% 3.33/1.51  BG Simplification    : 0.02
% 3.33/1.51  Subsumption          : 0.05
% 3.33/1.51  Abstraction          : 0.02
% 3.33/1.51  MUC search           : 0.00
% 3.33/1.51  Cooper               : 0.00
% 3.33/1.51  Total                : 0.74
% 3.33/1.51  Index Insertion      : 0.00
% 3.33/1.51  Index Deletion       : 0.00
% 3.33/1.51  Index Matching       : 0.00
% 3.33/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
