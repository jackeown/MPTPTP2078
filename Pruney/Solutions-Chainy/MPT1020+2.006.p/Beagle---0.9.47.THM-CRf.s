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
% DateTime   : Thu Dec  3 10:15:50 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  194 (26673 expanded)
%              Number of leaves         :   40 (8635 expanded)
%              Depth                    :   22
%              Number of atoms          :  447 (82010 expanded)
%              Number of equality atoms :   79 (15250 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k2_relat_1(A) = k1_xboole_0
              & k2_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_156,axiom,(
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

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) )
       => ( v1_funct_1(C)
          & v3_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_2)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_493,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_relset_1(A_130,B_131,D_132,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_502,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_493])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_99])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_139,plain,(
    ! [C_54,B_55,A_56] :
      ( v5_relat_1(C_54,B_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_152,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_139])).

tff(c_172,plain,(
    ! [B_65,A_66] :
      ( k2_relat_1(B_65) = A_66
      | ~ v2_funct_2(B_65,A_66)
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_178,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_152,c_172])).

tff(c_184,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_178])).

tff(c_387,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_463,plain,(
    ! [C_127,B_128,A_129] :
      ( v2_funct_2(C_127,B_128)
      | ~ v3_funct_2(C_127,A_129,B_128)
      | ~ v1_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_466,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_463])).

tff(c_478,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_466])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_478])).

tff(c_481,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_523,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | k2_relat_1(B_140) != k1_xboole_0
      | k2_relat_1(A_141) != k1_xboole_0
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_527,plain,(
    ! [A_141] :
      ( A_141 = '#skF_3'
      | k2_relat_1('#skF_3') != k1_xboole_0
      | k2_relat_1(A_141) != k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_108,c_523])).

tff(c_535,plain,(
    ! [A_141] :
      ( A_141 = '#skF_3'
      | k1_xboole_0 != '#skF_1'
      | k2_relat_1(A_141) != k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_527])).

tff(c_546,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_105,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_99])).

tff(c_111,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_153,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_175,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_153,c_172])).

tff(c_181,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_175])).

tff(c_185,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_66,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_354,plain,(
    ! [C_105,B_106,A_107] :
      ( v2_funct_2(C_105,B_106)
      | ~ v3_funct_2(C_105,A_107,B_106)
      | ~ v1_funct_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_360,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_354])).

tff(c_372,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_360])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_372])).

tff(c_375,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_506,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_512,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_506])).

tff(c_522,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_512])).

tff(c_551,plain,(
    ! [C_146,A_147,B_148] :
      ( v2_funct_1(C_146)
      | ~ v3_funct_2(C_146,A_147,B_148)
      | ~ v1_funct_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_557,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_551])).

tff(c_569,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_557])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_813,plain,(
    ! [C_188,D_189,B_190,A_191] :
      ( k2_funct_1(C_188) = D_189
      | k1_xboole_0 = B_190
      | k1_xboole_0 = A_191
      | ~ v2_funct_1(C_188)
      | ~ r2_relset_1(A_191,A_191,k1_partfun1(A_191,B_190,B_190,A_191,C_188,D_189),k6_partfun1(A_191))
      | k2_relset_1(A_191,B_190,C_188) != B_190
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(B_190,A_191)))
      | ~ v1_funct_2(D_189,B_190,A_191)
      | ~ v1_funct_1(D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190)))
      | ~ v1_funct_2(C_188,A_191,B_190)
      | ~ v1_funct_1(C_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_816,plain,
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
    inference(resolution,[status(thm)],[c_54,c_813])).

tff(c_819,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_56,c_522,c_569,c_816])).

tff(c_820,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_546,c_819])).

tff(c_660,plain,(
    ! [A_177,B_178] :
      ( k2_funct_2(A_177,B_178) = k2_funct_1(B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k2_zfmisc_1(A_177,A_177)))
      | ~ v3_funct_2(B_178,A_177,A_177)
      | ~ v1_funct_2(B_178,A_177,A_177)
      | ~ v1_funct_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_666,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_660])).

tff(c_680,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_666])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_687,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_52])).

tff(c_824,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_687])).

tff(c_831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_824])).

tff(c_833,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_842,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_6])).

tff(c_901,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_56])).

tff(c_499,plain,(
    ! [B_2,D_132] :
      ( r2_relset_1(k1_xboole_0,B_2,D_132,D_132)
      | ~ m1_subset_1(D_132,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_493])).

tff(c_1056,plain,(
    ! [B_218,D_219] :
      ( r2_relset_1('#skF_1',B_218,D_219,D_219)
      | ~ m1_subset_1(D_219,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_499])).

tff(c_1059,plain,(
    ! [B_218] : r2_relset_1('#skF_1',B_218,'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_901,c_1056])).

tff(c_964,plain,(
    ! [C_195,A_196,B_197] :
      ( v2_funct_1(C_195)
      | ~ v3_funct_2(C_195,A_196,B_197)
      | ~ v1_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1146,plain,(
    ! [C_237,B_238] :
      ( v2_funct_1(C_237)
      | ~ v3_funct_2(C_237,'#skF_1',B_238)
      | ~ v1_funct_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_964])).

tff(c_1148,plain,
    ( v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_1146])).

tff(c_1151,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_62,c_1148])).

tff(c_482,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_843,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_4])).

tff(c_1043,plain,(
    ! [C_212,A_213,B_214] :
      ( v3_funct_2(C_212,A_213,B_214)
      | ~ v2_funct_2(C_212,B_214)
      | ~ v2_funct_1(C_212)
      | ~ v1_funct_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1187,plain,(
    ! [C_250,A_251] :
      ( v3_funct_2(C_250,A_251,'#skF_1')
      | ~ v2_funct_2(C_250,'#skF_1')
      | ~ v2_funct_1(C_250)
      | ~ v1_funct_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1043])).

tff(c_1189,plain,(
    ! [A_251] :
      ( v3_funct_2('#skF_3',A_251,'#skF_1')
      | ~ v2_funct_2('#skF_3','#skF_1')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_901,c_1187])).

tff(c_1192,plain,(
    ! [A_251] : v3_funct_2('#skF_3',A_251,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1151,c_482,c_1189])).

tff(c_1158,plain,(
    ! [A_241,B_242] :
      ( k2_funct_2(A_241,B_242) = k2_funct_1(B_242)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(k2_zfmisc_1(A_241,A_241)))
      | ~ v3_funct_2(B_242,A_241,A_241)
      | ~ v1_funct_2(B_242,A_241,A_241)
      | ~ v1_funct_1(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1267,plain,(
    ! [B_261] :
      ( k2_funct_2('#skF_1',B_261) = k2_funct_1(B_261)
      | ~ m1_subset_1(B_261,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_261,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_261,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1158])).

tff(c_1270,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_901,c_1267])).

tff(c_1273,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1192,c_1270])).

tff(c_1280,plain,(
    ! [A_262,B_263] :
      ( m1_subset_1(k2_funct_2(A_262,B_263),k1_zfmisc_1(k2_zfmisc_1(A_262,A_262)))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(k2_zfmisc_1(A_262,A_262)))
      | ~ v3_funct_2(B_263,A_262,A_262)
      | ~ v1_funct_2(B_263,A_262,A_262)
      | ~ v1_funct_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1319,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_1280])).

tff(c_1344,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1192,c_901,c_842,c_842,c_1319])).

tff(c_123,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,(
    ! [C_50] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_123])).

tff(c_839,plain,(
    ! [C_50] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_131])).

tff(c_1393,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1344,c_839])).

tff(c_832,plain,(
    ! [A_141] :
      ( A_141 = '#skF_3'
      | k2_relat_1(A_141) != k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_977,plain,(
    ! [A_141] :
      ( A_141 = '#skF_3'
      | k2_relat_1(A_141) != '#skF_1'
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_832])).

tff(c_1403,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1393,c_977])).

tff(c_1443,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1403])).

tff(c_1137,plain,(
    ! [A_235,B_236] :
      ( v1_funct_1(k2_funct_2(A_235,B_236))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ v3_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1260,plain,(
    ! [B_260] :
      ( v1_funct_1(k2_funct_2('#skF_1',B_260))
      | ~ m1_subset_1(B_260,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_260,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_260,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1137])).

tff(c_1263,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_901,c_1260])).

tff(c_1266,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1192,c_1263])).

tff(c_1274,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_1266])).

tff(c_1049,plain,(
    ! [C_212,B_2] :
      ( v3_funct_2(C_212,'#skF_1',B_2)
      | ~ v2_funct_2(C_212,B_2)
      | ~ v2_funct_1(C_212)
      | ~ v1_funct_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_1043])).

tff(c_1354,plain,(
    ! [B_2] :
      ( v3_funct_2(k2_funct_1('#skF_3'),'#skF_1',B_2)
      | ~ v2_funct_2(k2_funct_1('#skF_3'),B_2)
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1344,c_1049])).

tff(c_1383,plain,(
    ! [B_2] :
      ( v3_funct_2(k2_funct_1('#skF_3'),'#skF_1',B_2)
      | ~ v2_funct_2(k2_funct_1('#skF_3'),B_2)
      | ~ v2_funct_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1354])).

tff(c_1472,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1383])).

tff(c_1141,plain,(
    ! [B_236] :
      ( v1_funct_1(k2_funct_2('#skF_1',B_236))
      | ~ m1_subset_1(B_236,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_236,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_236,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1137])).

tff(c_1352,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1344,c_1141])).

tff(c_1380,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1352])).

tff(c_1486,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1380])).

tff(c_1193,plain,(
    ! [A_252,B_253] :
      ( v1_funct_2(k2_funct_2(A_252,B_253),A_252,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(k2_zfmisc_1(A_252,A_252)))
      | ~ v3_funct_2(B_253,A_252,A_252)
      | ~ v1_funct_2(B_253,A_252,A_252)
      | ~ v1_funct_1(B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1586,plain,(
    ! [B_284] :
      ( v1_funct_2(k2_funct_2('#skF_1',B_284),'#skF_1','#skF_1')
      | ~ m1_subset_1(B_284,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_284,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_284,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1193])).

tff(c_1589,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_1586])).

tff(c_1591,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1192,c_901,c_1589])).

tff(c_1593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1486,c_1591])).

tff(c_1594,plain,
    ( ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_1596,plain,(
    ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1594])).

tff(c_1253,plain,(
    ! [A_258,B_259] :
      ( v3_funct_2(k2_funct_2(A_258,B_259),A_258,A_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258)))
      | ~ v3_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1664,plain,(
    ! [B_287] :
      ( v3_funct_2(k2_funct_2('#skF_1',B_287),'#skF_1','#skF_1')
      | ~ m1_subset_1(B_287,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_287,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_287,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_1253])).

tff(c_1675,plain,
    ( v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_1664])).

tff(c_1681,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1192,c_901,c_1675])).

tff(c_1683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1596,c_1681])).

tff(c_1685,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1594])).

tff(c_967,plain,(
    ! [C_195,A_1] :
      ( v2_funct_1(C_195)
      | ~ v3_funct_2(C_195,A_1,'#skF_1')
      | ~ v1_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_964])).

tff(c_1691,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1685,c_967])).

tff(c_1702,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_1274,c_1691])).

tff(c_1704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1472,c_1702])).

tff(c_1706,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1383])).

tff(c_1046,plain,(
    ! [C_212,A_1] :
      ( v3_funct_2(C_212,A_1,'#skF_1')
      | ~ v2_funct_2(C_212,'#skF_1')
      | ~ v2_funct_1(C_212)
      | ~ v1_funct_1(C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1043])).

tff(c_1356,plain,(
    ! [A_1] :
      ( v3_funct_2(k2_funct_1('#skF_3'),A_1,'#skF_1')
      | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1344,c_1046])).

tff(c_1386,plain,(
    ! [A_1] :
      ( v3_funct_2(k2_funct_1('#skF_3'),A_1,'#skF_1')
      | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
      | ~ v2_funct_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1356])).

tff(c_1731,plain,(
    ! [A_1] :
      ( v3_funct_2(k2_funct_1('#skF_3'),A_1,'#skF_1')
      | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_1386])).

tff(c_1732,plain,(
    ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1731])).

tff(c_1761,plain,(
    ! [B_292] :
      ( v3_funct_2(k2_funct_2('#skF_1',B_292),'#skF_1','#skF_1')
      | ~ m1_subset_1(B_292,k1_zfmisc_1('#skF_1'))
      | ~ v3_funct_2(B_292,'#skF_1','#skF_1')
      | ~ v1_funct_2(B_292,'#skF_1','#skF_1')
      | ~ v1_funct_1(B_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_1253])).

tff(c_1772,plain,
    ( v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_1761])).

tff(c_1778,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1192,c_901,c_1772])).

tff(c_1004,plain,(
    ! [C_205,B_206,A_207] :
      ( v2_funct_2(C_205,B_206)
      | ~ v3_funct_2(C_205,A_207,B_206)
      | ~ v1_funct_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1010,plain,(
    ! [C_205,B_2] :
      ( v2_funct_2(C_205,B_2)
      | ~ v3_funct_2(C_205,'#skF_1',B_2)
      | ~ v1_funct_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_1004])).

tff(c_1780,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1778,c_1010])).

tff(c_1789,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_1274,c_1780])).

tff(c_1791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_1789])).

tff(c_1793,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1731])).

tff(c_148,plain,(
    ! [C_54,B_2] :
      ( v5_relat_1(C_54,B_2)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_139])).

tff(c_838,plain,(
    ! [C_54,B_2] :
      ( v5_relat_1(C_54,B_2)
      | ~ m1_subset_1(C_54,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_148])).

tff(c_1405,plain,(
    ! [B_264] : v5_relat_1(k2_funct_1('#skF_3'),B_264) ),
    inference(resolution,[status(thm)],[c_1344,c_838])).

tff(c_38,plain,(
    ! [B_31,A_30] :
      ( k2_relat_1(B_31) = A_30
      | ~ v2_funct_2(B_31,A_30)
      | ~ v5_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1408,plain,(
    ! [B_264] :
      ( k2_relat_1(k2_funct_1('#skF_3')) = B_264
      | ~ v2_funct_2(k2_funct_1('#skF_3'),B_264)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1405,c_38])).

tff(c_1415,plain,(
    ! [B_264] :
      ( k2_relat_1(k2_funct_1('#skF_3')) = B_264
      | ~ v2_funct_2(k2_funct_1('#skF_3'),B_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1393,c_1408])).

tff(c_1796,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1793,c_1415])).

tff(c_1800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1443,c_1796])).

tff(c_1801,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1403])).

tff(c_525,plain,(
    ! [A_141] :
      ( A_141 = '#skF_2'
      | k2_relat_1('#skF_2') != k1_xboole_0
      | k2_relat_1(A_141) != k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_111,c_523])).

tff(c_533,plain,(
    ! [A_141] :
      ( A_141 = '#skF_2'
      | k1_xboole_0 != '#skF_1'
      | k2_relat_1(A_141) != k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_525])).

tff(c_850,plain,(
    ! [A_192] :
      ( A_192 = '#skF_2'
      | k2_relat_1(A_192) != '#skF_1'
      | ~ v1_relat_1(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_833,c_533])).

tff(c_859,plain,
    ( '#skF_2' = '#skF_3'
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_108,c_850])).

tff(c_870,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_859])).

tff(c_881,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_52])).

tff(c_1275,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_881])).

tff(c_1816,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1801,c_1275])).

tff(c_1829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1059,c_1816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.79  
% 4.50/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.80  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.50/1.80  
% 4.50/1.80  %Foreground sorts:
% 4.50/1.80  
% 4.50/1.80  
% 4.50/1.80  %Background operators:
% 4.50/1.80  
% 4.50/1.80  
% 4.50/1.80  %Foreground operators:
% 4.50/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.50/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.50/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.50/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.80  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.50/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.80  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.50/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.50/1.80  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.50/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.50/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.80  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.50/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.50/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.80  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.50/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.50/1.80  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.50/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.80  
% 4.50/1.83  tff(f_178, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 4.50/1.83  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.50/1.83  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.50/1.83  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.50/1.83  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.50/1.83  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.50/1.83  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.50/1.83  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t197_relat_1)).
% 4.50/1.83  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.50/1.83  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 4.50/1.83  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.50/1.83  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.50/1.83  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B)) => (v1_funct_1(C) & v3_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_2)).
% 4.50/1.83  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.50/1.83  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.50/1.83  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_493, plain, (![A_130, B_131, D_132]: (r2_relset_1(A_130, B_131, D_132, D_132) | ~m1_subset_1(D_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.50/1.83  tff(c_502, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_493])).
% 4.50/1.83  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.50/1.83  tff(c_99, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.50/1.83  tff(c_102, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_99])).
% 4.50/1.83  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_102])).
% 4.50/1.83  tff(c_139, plain, (![C_54, B_55, A_56]: (v5_relat_1(C_54, B_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.50/1.83  tff(c_152, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_139])).
% 4.50/1.83  tff(c_172, plain, (![B_65, A_66]: (k2_relat_1(B_65)=A_66 | ~v2_funct_2(B_65, A_66) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.50/1.83  tff(c_178, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_152, c_172])).
% 4.50/1.83  tff(c_184, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_178])).
% 4.50/1.83  tff(c_387, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_184])).
% 4.50/1.83  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_463, plain, (![C_127, B_128, A_129]: (v2_funct_2(C_127, B_128) | ~v3_funct_2(C_127, A_129, B_128) | ~v1_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.50/1.83  tff(c_466, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_463])).
% 4.50/1.83  tff(c_478, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_466])).
% 4.50/1.83  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_478])).
% 4.50/1.83  tff(c_481, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_184])).
% 4.50/1.83  tff(c_523, plain, (![B_140, A_141]: (B_140=A_141 | k2_relat_1(B_140)!=k1_xboole_0 | k2_relat_1(A_141)!=k1_xboole_0 | ~v1_relat_1(B_140) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.50/1.83  tff(c_527, plain, (![A_141]: (A_141='#skF_3' | k2_relat_1('#skF_3')!=k1_xboole_0 | k2_relat_1(A_141)!=k1_xboole_0 | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_108, c_523])).
% 4.50/1.83  tff(c_535, plain, (![A_141]: (A_141='#skF_3' | k1_xboole_0!='#skF_1' | k2_relat_1(A_141)!=k1_xboole_0 | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_527])).
% 4.50/1.83  tff(c_546, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_535])).
% 4.50/1.83  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_68, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_105, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_99])).
% 4.50/1.83  tff(c_111, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_105])).
% 4.50/1.83  tff(c_153, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_139])).
% 4.50/1.83  tff(c_175, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_153, c_172])).
% 4.50/1.83  tff(c_181, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_175])).
% 4.50/1.83  tff(c_185, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_181])).
% 4.50/1.83  tff(c_66, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_354, plain, (![C_105, B_106, A_107]: (v2_funct_2(C_105, B_106) | ~v3_funct_2(C_105, A_107, B_106) | ~v1_funct_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.50/1.83  tff(c_360, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_354])).
% 4.50/1.83  tff(c_372, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_360])).
% 4.50/1.83  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_372])).
% 4.50/1.83  tff(c_375, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_181])).
% 4.50/1.83  tff(c_506, plain, (![A_137, B_138, C_139]: (k2_relset_1(A_137, B_138, C_139)=k2_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.50/1.83  tff(c_512, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_506])).
% 4.50/1.83  tff(c_522, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_512])).
% 4.50/1.83  tff(c_551, plain, (![C_146, A_147, B_148]: (v2_funct_1(C_146) | ~v3_funct_2(C_146, A_147, B_148) | ~v1_funct_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.50/1.83  tff(c_557, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_551])).
% 4.50/1.83  tff(c_569, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_557])).
% 4.50/1.83  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_813, plain, (![C_188, D_189, B_190, A_191]: (k2_funct_1(C_188)=D_189 | k1_xboole_0=B_190 | k1_xboole_0=A_191 | ~v2_funct_1(C_188) | ~r2_relset_1(A_191, A_191, k1_partfun1(A_191, B_190, B_190, A_191, C_188, D_189), k6_partfun1(A_191)) | k2_relset_1(A_191, B_190, C_188)!=B_190 | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(B_190, A_191))) | ~v1_funct_2(D_189, B_190, A_191) | ~v1_funct_1(D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))) | ~v1_funct_2(C_188, A_191, B_190) | ~v1_funct_1(C_188))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.50/1.83  tff(c_816, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_813])).
% 4.50/1.83  tff(c_819, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_56, c_522, c_569, c_816])).
% 4.50/1.83  tff(c_820, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_546, c_819])).
% 4.50/1.83  tff(c_660, plain, (![A_177, B_178]: (k2_funct_2(A_177, B_178)=k2_funct_1(B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(k2_zfmisc_1(A_177, A_177))) | ~v3_funct_2(B_178, A_177, A_177) | ~v1_funct_2(B_178, A_177, A_177) | ~v1_funct_1(B_178))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.50/1.83  tff(c_666, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_660])).
% 4.50/1.83  tff(c_680, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_666])).
% 4.50/1.83  tff(c_52, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.50/1.83  tff(c_687, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_52])).
% 4.50/1.83  tff(c_824, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_687])).
% 4.50/1.83  tff(c_831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_502, c_824])).
% 4.50/1.83  tff(c_833, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_535])).
% 4.50/1.83  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.83  tff(c_842, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_6])).
% 4.50/1.83  tff(c_901, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_842, c_56])).
% 4.50/1.83  tff(c_499, plain, (![B_2, D_132]: (r2_relset_1(k1_xboole_0, B_2, D_132, D_132) | ~m1_subset_1(D_132, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_493])).
% 4.50/1.83  tff(c_1056, plain, (![B_218, D_219]: (r2_relset_1('#skF_1', B_218, D_219, D_219) | ~m1_subset_1(D_219, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_499])).
% 4.50/1.83  tff(c_1059, plain, (![B_218]: (r2_relset_1('#skF_1', B_218, '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_901, c_1056])).
% 4.50/1.83  tff(c_964, plain, (![C_195, A_196, B_197]: (v2_funct_1(C_195) | ~v3_funct_2(C_195, A_196, B_197) | ~v1_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.50/1.83  tff(c_1146, plain, (![C_237, B_238]: (v2_funct_1(C_237) | ~v3_funct_2(C_237, '#skF_1', B_238) | ~v1_funct_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_842, c_964])).
% 4.50/1.83  tff(c_1148, plain, (v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_58, c_1146])).
% 4.50/1.83  tff(c_1151, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_901, c_62, c_1148])).
% 4.50/1.83  tff(c_482, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 4.50/1.83  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/1.83  tff(c_843, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_4])).
% 4.50/1.83  tff(c_1043, plain, (![C_212, A_213, B_214]: (v3_funct_2(C_212, A_213, B_214) | ~v2_funct_2(C_212, B_214) | ~v2_funct_1(C_212) | ~v1_funct_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.50/1.83  tff(c_1187, plain, (![C_250, A_251]: (v3_funct_2(C_250, A_251, '#skF_1') | ~v2_funct_2(C_250, '#skF_1') | ~v2_funct_1(C_250) | ~v1_funct_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1043])).
% 4.50/1.83  tff(c_1189, plain, (![A_251]: (v3_funct_2('#skF_3', A_251, '#skF_1') | ~v2_funct_2('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_901, c_1187])).
% 4.50/1.83  tff(c_1192, plain, (![A_251]: (v3_funct_2('#skF_3', A_251, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1151, c_482, c_1189])).
% 4.50/1.83  tff(c_1158, plain, (![A_241, B_242]: (k2_funct_2(A_241, B_242)=k2_funct_1(B_242) | ~m1_subset_1(B_242, k1_zfmisc_1(k2_zfmisc_1(A_241, A_241))) | ~v3_funct_2(B_242, A_241, A_241) | ~v1_funct_2(B_242, A_241, A_241) | ~v1_funct_1(B_242))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.50/1.83  tff(c_1267, plain, (![B_261]: (k2_funct_2('#skF_1', B_261)=k2_funct_1(B_261) | ~m1_subset_1(B_261, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_261, '#skF_1', '#skF_1') | ~v1_funct_2(B_261, '#skF_1', '#skF_1') | ~v1_funct_1(B_261))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1158])).
% 4.50/1.83  tff(c_1270, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_901, c_1267])).
% 4.50/1.83  tff(c_1273, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1192, c_1270])).
% 4.50/1.83  tff(c_1280, plain, (![A_262, B_263]: (m1_subset_1(k2_funct_2(A_262, B_263), k1_zfmisc_1(k2_zfmisc_1(A_262, A_262))) | ~m1_subset_1(B_263, k1_zfmisc_1(k2_zfmisc_1(A_262, A_262))) | ~v3_funct_2(B_263, A_262, A_262) | ~v1_funct_2(B_263, A_262, A_262) | ~v1_funct_1(B_263))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.50/1.83  tff(c_1319, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1273, c_1280])).
% 4.50/1.83  tff(c_1344, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1192, c_901, c_842, c_842, c_1319])).
% 4.50/1.83  tff(c_123, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.50/1.83  tff(c_131, plain, (![C_50]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_123])).
% 4.50/1.83  tff(c_839, plain, (![C_50]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_131])).
% 4.50/1.83  tff(c_1393, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1344, c_839])).
% 4.50/1.83  tff(c_832, plain, (![A_141]: (A_141='#skF_3' | k2_relat_1(A_141)!=k1_xboole_0 | ~v1_relat_1(A_141))), inference(splitRight, [status(thm)], [c_535])).
% 4.50/1.83  tff(c_977, plain, (![A_141]: (A_141='#skF_3' | k2_relat_1(A_141)!='#skF_1' | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_832])).
% 4.50/1.83  tff(c_1403, plain, (k2_funct_1('#skF_3')='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(resolution, [status(thm)], [c_1393, c_977])).
% 4.50/1.83  tff(c_1443, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_1403])).
% 4.50/1.83  tff(c_1137, plain, (![A_235, B_236]: (v1_funct_1(k2_funct_2(A_235, B_236)) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~v3_funct_2(B_236, A_235, A_235) | ~v1_funct_2(B_236, A_235, A_235) | ~v1_funct_1(B_236))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.50/1.83  tff(c_1260, plain, (![B_260]: (v1_funct_1(k2_funct_2('#skF_1', B_260)) | ~m1_subset_1(B_260, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_260, '#skF_1', '#skF_1') | ~v1_funct_2(B_260, '#skF_1', '#skF_1') | ~v1_funct_1(B_260))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1137])).
% 4.50/1.83  tff(c_1263, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_901, c_1260])).
% 4.50/1.83  tff(c_1266, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1192, c_1263])).
% 4.50/1.83  tff(c_1274, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_1266])).
% 4.50/1.83  tff(c_1049, plain, (![C_212, B_2]: (v3_funct_2(C_212, '#skF_1', B_2) | ~v2_funct_2(C_212, B_2) | ~v2_funct_1(C_212) | ~v1_funct_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_842, c_1043])).
% 4.50/1.83  tff(c_1354, plain, (![B_2]: (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', B_2) | ~v2_funct_2(k2_funct_1('#skF_3'), B_2) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1344, c_1049])).
% 4.50/1.83  tff(c_1383, plain, (![B_2]: (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', B_2) | ~v2_funct_2(k2_funct_1('#skF_3'), B_2) | ~v2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1354])).
% 4.50/1.83  tff(c_1472, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1383])).
% 4.50/1.83  tff(c_1141, plain, (![B_236]: (v1_funct_1(k2_funct_2('#skF_1', B_236)) | ~m1_subset_1(B_236, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_236, '#skF_1', '#skF_1') | ~v1_funct_2(B_236, '#skF_1', '#skF_1') | ~v1_funct_1(B_236))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1137])).
% 4.50/1.83  tff(c_1352, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1344, c_1141])).
% 4.50/1.83  tff(c_1380, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1352])).
% 4.50/1.83  tff(c_1486, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1380])).
% 4.50/1.83  tff(c_1193, plain, (![A_252, B_253]: (v1_funct_2(k2_funct_2(A_252, B_253), A_252, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(k2_zfmisc_1(A_252, A_252))) | ~v3_funct_2(B_253, A_252, A_252) | ~v1_funct_2(B_253, A_252, A_252) | ~v1_funct_1(B_253))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.50/1.83  tff(c_1586, plain, (![B_284]: (v1_funct_2(k2_funct_2('#skF_1', B_284), '#skF_1', '#skF_1') | ~m1_subset_1(B_284, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_284, '#skF_1', '#skF_1') | ~v1_funct_2(B_284, '#skF_1', '#skF_1') | ~v1_funct_1(B_284))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1193])).
% 4.50/1.83  tff(c_1589, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1273, c_1586])).
% 4.50/1.83  tff(c_1591, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1192, c_901, c_1589])).
% 4.50/1.83  tff(c_1593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1486, c_1591])).
% 4.50/1.83  tff(c_1594, plain, (~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1380])).
% 4.50/1.83  tff(c_1596, plain, (~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1594])).
% 4.50/1.83  tff(c_1253, plain, (![A_258, B_259]: (v3_funct_2(k2_funct_2(A_258, B_259), A_258, A_258) | ~m1_subset_1(B_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))) | ~v3_funct_2(B_259, A_258, A_258) | ~v1_funct_2(B_259, A_258, A_258) | ~v1_funct_1(B_259))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.50/1.83  tff(c_1664, plain, (![B_287]: (v3_funct_2(k2_funct_2('#skF_1', B_287), '#skF_1', '#skF_1') | ~m1_subset_1(B_287, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_287, '#skF_1', '#skF_1') | ~v1_funct_2(B_287, '#skF_1', '#skF_1') | ~v1_funct_1(B_287))), inference(superposition, [status(thm), theory('equality')], [c_842, c_1253])).
% 4.50/1.83  tff(c_1675, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1273, c_1664])).
% 4.50/1.83  tff(c_1681, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1192, c_901, c_1675])).
% 4.50/1.83  tff(c_1683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1596, c_1681])).
% 4.50/1.83  tff(c_1685, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_1594])).
% 4.50/1.83  tff(c_967, plain, (![C_195, A_1]: (v2_funct_1(C_195) | ~v3_funct_2(C_195, A_1, '#skF_1') | ~v1_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_843, c_964])).
% 4.50/1.83  tff(c_1691, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1685, c_967])).
% 4.50/1.83  tff(c_1702, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_1274, c_1691])).
% 4.50/1.83  tff(c_1704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1472, c_1702])).
% 4.50/1.83  tff(c_1706, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1383])).
% 4.50/1.83  tff(c_1046, plain, (![C_212, A_1]: (v3_funct_2(C_212, A_1, '#skF_1') | ~v2_funct_2(C_212, '#skF_1') | ~v2_funct_1(C_212) | ~v1_funct_1(C_212) | ~m1_subset_1(C_212, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1043])).
% 4.50/1.83  tff(c_1356, plain, (![A_1]: (v3_funct_2(k2_funct_1('#skF_3'), A_1, '#skF_1') | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1344, c_1046])).
% 4.50/1.83  tff(c_1386, plain, (![A_1]: (v3_funct_2(k2_funct_1('#skF_3'), A_1, '#skF_1') | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_1356])).
% 4.50/1.83  tff(c_1731, plain, (![A_1]: (v3_funct_2(k2_funct_1('#skF_3'), A_1, '#skF_1') | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_1386])).
% 4.50/1.83  tff(c_1732, plain, (~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1731])).
% 4.50/1.83  tff(c_1761, plain, (![B_292]: (v3_funct_2(k2_funct_2('#skF_1', B_292), '#skF_1', '#skF_1') | ~m1_subset_1(B_292, k1_zfmisc_1('#skF_1')) | ~v3_funct_2(B_292, '#skF_1', '#skF_1') | ~v1_funct_2(B_292, '#skF_1', '#skF_1') | ~v1_funct_1(B_292))), inference(superposition, [status(thm), theory('equality')], [c_843, c_1253])).
% 4.50/1.83  tff(c_1772, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1273, c_1761])).
% 4.50/1.83  tff(c_1778, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1192, c_901, c_1772])).
% 4.50/1.83  tff(c_1004, plain, (![C_205, B_206, A_207]: (v2_funct_2(C_205, B_206) | ~v3_funct_2(C_205, A_207, B_206) | ~v1_funct_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.50/1.83  tff(c_1010, plain, (![C_205, B_2]: (v2_funct_2(C_205, B_2) | ~v3_funct_2(C_205, '#skF_1', B_2) | ~v1_funct_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_842, c_1004])).
% 4.50/1.83  tff(c_1780, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1778, c_1010])).
% 4.50/1.83  tff(c_1789, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_1274, c_1780])).
% 4.50/1.83  tff(c_1791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1732, c_1789])).
% 4.50/1.83  tff(c_1793, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_1731])).
% 4.50/1.83  tff(c_148, plain, (![C_54, B_2]: (v5_relat_1(C_54, B_2) | ~m1_subset_1(C_54, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_139])).
% 4.50/1.83  tff(c_838, plain, (![C_54, B_2]: (v5_relat_1(C_54, B_2) | ~m1_subset_1(C_54, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_148])).
% 4.50/1.83  tff(c_1405, plain, (![B_264]: (v5_relat_1(k2_funct_1('#skF_3'), B_264))), inference(resolution, [status(thm)], [c_1344, c_838])).
% 4.50/1.83  tff(c_38, plain, (![B_31, A_30]: (k2_relat_1(B_31)=A_30 | ~v2_funct_2(B_31, A_30) | ~v5_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.50/1.83  tff(c_1408, plain, (![B_264]: (k2_relat_1(k2_funct_1('#skF_3'))=B_264 | ~v2_funct_2(k2_funct_1('#skF_3'), B_264) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1405, c_38])).
% 4.50/1.83  tff(c_1415, plain, (![B_264]: (k2_relat_1(k2_funct_1('#skF_3'))=B_264 | ~v2_funct_2(k2_funct_1('#skF_3'), B_264))), inference(demodulation, [status(thm), theory('equality')], [c_1393, c_1408])).
% 4.50/1.83  tff(c_1796, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_1793, c_1415])).
% 4.50/1.83  tff(c_1800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1443, c_1796])).
% 4.50/1.83  tff(c_1801, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1403])).
% 4.50/1.83  tff(c_525, plain, (![A_141]: (A_141='#skF_2' | k2_relat_1('#skF_2')!=k1_xboole_0 | k2_relat_1(A_141)!=k1_xboole_0 | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_111, c_523])).
% 4.50/1.83  tff(c_533, plain, (![A_141]: (A_141='#skF_2' | k1_xboole_0!='#skF_1' | k2_relat_1(A_141)!=k1_xboole_0 | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_525])).
% 4.50/1.83  tff(c_850, plain, (![A_192]: (A_192='#skF_2' | k2_relat_1(A_192)!='#skF_1' | ~v1_relat_1(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_833, c_833, c_533])).
% 4.50/1.83  tff(c_859, plain, ('#skF_2'='#skF_3' | k2_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_108, c_850])).
% 4.50/1.83  tff(c_870, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_859])).
% 4.50/1.83  tff(c_881, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_52])).
% 4.50/1.83  tff(c_1275, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_881])).
% 4.50/1.83  tff(c_1816, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1801, c_1275])).
% 4.50/1.83  tff(c_1829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1059, c_1816])).
% 4.50/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.83  
% 4.50/1.83  Inference rules
% 4.50/1.83  ----------------------
% 4.50/1.83  #Ref     : 0
% 4.50/1.83  #Sup     : 383
% 4.50/1.83  #Fact    : 0
% 4.50/1.83  #Define  : 0
% 4.50/1.83  #Split   : 25
% 4.50/1.83  #Chain   : 0
% 4.50/1.83  #Close   : 0
% 4.50/1.83  
% 4.50/1.83  Ordering : KBO
% 4.50/1.83  
% 4.50/1.83  Simplification rules
% 4.50/1.83  ----------------------
% 4.50/1.83  #Subsume      : 57
% 4.50/1.83  #Demod        : 394
% 4.50/1.83  #Tautology    : 139
% 4.50/1.83  #SimpNegUnit  : 9
% 4.50/1.83  #BackRed      : 46
% 4.50/1.83  
% 4.50/1.83  #Partial instantiations: 0
% 4.50/1.83  #Strategies tried      : 1
% 4.50/1.83  
% 4.50/1.83  Timing (in seconds)
% 4.50/1.83  ----------------------
% 4.50/1.83  Preprocessing        : 0.37
% 4.75/1.83  Parsing              : 0.20
% 4.75/1.83  CNF conversion       : 0.02
% 4.75/1.83  Main loop            : 0.63
% 4.75/1.83  Inferencing          : 0.22
% 4.75/1.83  Reduction            : 0.22
% 4.75/1.83  Demodulation         : 0.16
% 4.75/1.83  BG Simplification    : 0.03
% 4.75/1.83  Subsumption          : 0.11
% 4.75/1.83  Abstraction          : 0.03
% 4.75/1.83  MUC search           : 0.00
% 4.75/1.83  Cooper               : 0.00
% 4.75/1.83  Total                : 1.07
% 4.75/1.83  Index Insertion      : 0.00
% 4.75/1.83  Index Deletion       : 0.00
% 4.75/1.83  Index Matching       : 0.00
% 4.75/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
