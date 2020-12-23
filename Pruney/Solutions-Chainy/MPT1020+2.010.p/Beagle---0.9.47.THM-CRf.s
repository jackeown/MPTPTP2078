%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:51 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :  168 (5057 expanded)
%              Number of leaves         :   44 (1635 expanded)
%              Depth                    :   23
%              Number of atoms          :  345 (15069 expanded)
%              Number of equality atoms :   88 (2761 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k2_relat_1(A) = k1_xboole_0
              & k2_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

tff(f_63,axiom,(
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

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_107,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_103,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_139,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_150,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_139])).

tff(c_174,plain,(
    ! [B_63,A_64] :
      ( k2_relat_1(B_63) = A_64
      | ~ v2_funct_2(B_63,A_64)
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_150,c_174])).

tff(c_192,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_183])).

tff(c_683,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_929,plain,(
    ! [C_140,B_141,A_142] :
      ( v2_funct_2(C_140,B_141)
      | ~ v3_funct_2(C_140,A_142,B_141)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_935,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_929])).

tff(c_943,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_935])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_943])).

tff(c_946,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_958,plain,(
    ! [A_143,B_144,D_145] :
      ( r2_relset_1(A_143,B_144,D_145,D_145)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_966,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_958])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_112,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_103])).

tff(c_121,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_112])).

tff(c_151,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_139])).

tff(c_180,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_151,c_174])).

tff(c_189,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_180])).

tff(c_193,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_70,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_66,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_651,plain,(
    ! [C_110,B_111,A_112] :
      ( v2_funct_2(C_110,B_111)
      | ~ v3_funct_2(C_110,A_112,B_111)
      | ~ v1_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_660,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_651])).

tff(c_668,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_660])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_668])).

tff(c_671,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_969,plain,(
    ! [B_147,A_148] :
      ( B_147 = A_148
      | k2_relat_1(B_147) != k1_xboole_0
      | k2_relat_1(A_148) != k1_xboole_0
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_973,plain,(
    ! [A_148] :
      ( A_148 = '#skF_2'
      | k2_relat_1('#skF_2') != k1_xboole_0
      | k2_relat_1(A_148) != k1_xboole_0
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_121,c_969])).

tff(c_981,plain,(
    ! [A_148] :
      ( A_148 = '#skF_2'
      | k1_xboole_0 != '#skF_1'
      | k2_relat_1(A_148) != k1_xboole_0
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_973])).

tff(c_985,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_981])).

tff(c_68,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_986,plain,(
    ! [A_149,B_150,C_151] :
      ( k2_relset_1(A_149,B_150,C_151) = k2_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_995,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_986])).

tff(c_1001,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_995])).

tff(c_1143,plain,(
    ! [C_159,A_160,B_161] :
      ( v2_funct_1(C_159)
      | ~ v3_funct_2(C_159,A_160,B_161)
      | ~ v1_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1152,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1143])).

tff(c_1159,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1152])).

tff(c_54,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1737,plain,(
    ! [C_213,D_214,B_215,A_216] :
      ( k2_funct_1(C_213) = D_214
      | k1_xboole_0 = B_215
      | k1_xboole_0 = A_216
      | ~ v2_funct_1(C_213)
      | ~ r2_relset_1(A_216,A_216,k1_partfun1(A_216,B_215,B_215,A_216,C_213,D_214),k6_partfun1(A_216))
      | k2_relset_1(A_216,B_215,C_213) != B_215
      | ~ m1_subset_1(D_214,k1_zfmisc_1(k2_zfmisc_1(B_215,A_216)))
      | ~ v1_funct_2(D_214,B_215,A_216)
      | ~ v1_funct_1(D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215)))
      | ~ v1_funct_2(C_213,A_216,B_215)
      | ~ v1_funct_1(C_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1746,plain,
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
    inference(resolution,[status(thm)],[c_54,c_1737])).

tff(c_1749,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_60,c_56,c_1001,c_1159,c_1746])).

tff(c_1750,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_985,c_1749])).

tff(c_1405,plain,(
    ! [A_190,B_191] :
      ( k2_funct_2(A_190,B_191) = k2_funct_1(B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1417,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1405])).

tff(c_1425,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1417])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1432,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_52])).

tff(c_1758,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1750,c_1432])).

tff(c_1769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_1758])).

tff(c_1771,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_981])).

tff(c_1770,plain,(
    ! [A_148] :
      ( A_148 = '#skF_2'
      | k2_relat_1(A_148) != k1_xboole_0
      | ~ v1_relat_1(A_148) ) ),
    inference(splitRight,[status(thm)],[c_981])).

tff(c_1778,plain,(
    ! [A_217] :
      ( A_217 = '#skF_2'
      | k2_relat_1(A_217) != '#skF_1'
      | ~ v1_relat_1(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1771,c_1770])).

tff(c_1787,plain,
    ( '#skF_2' = '#skF_3'
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_118,c_1778])).

tff(c_1799,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_1787])).

tff(c_48,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,(
    ! [A_9] : k2_relat_1(k6_partfun1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_44,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_106,plain,(
    ! [A_30] :
      ( v1_relat_1(k6_partfun1(A_30))
      | ~ v1_relat_1(k2_zfmisc_1(A_30,A_30)) ) ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_115,plain,(
    ! [A_30] : v1_relat_1(k6_partfun1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_1781,plain,(
    ! [A_30] :
      ( k6_partfun1(A_30) = '#skF_2'
      | k2_relat_1(k6_partfun1(A_30)) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_115,c_1778])).

tff(c_1792,plain,(
    ! [A_30] :
      ( k6_partfun1(A_30) = '#skF_2'
      | A_30 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1781])).

tff(c_1830,plain,(
    ! [A_218] :
      ( k6_partfun1(A_218) = '#skF_3'
      | A_218 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_1792])).

tff(c_1967,plain,(
    ! [A_232] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_232,A_232)))
      | A_232 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_44])).

tff(c_20,plain,(
    ! [A_19,B_20,D_22] :
      ( r2_relset_1(A_19,B_20,D_22,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2022,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1967,c_20])).

tff(c_1965,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_44])).

tff(c_1853,plain,(
    ! [A_218] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_218,A_218)))
      | A_218 != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_44])).

tff(c_2447,plain,(
    ! [A_274,B_275] :
      ( k2_funct_2(A_274,B_275) = k2_funct_1(B_275)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_zfmisc_1(A_274,A_274)))
      | ~ v3_funct_2(B_275,A_274,A_274)
      | ~ v1_funct_2(B_275,A_274,A_274)
      | ~ v1_funct_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2453,plain,(
    ! [A_218] :
      ( k2_funct_2(A_218,'#skF_3') = k2_funct_1('#skF_3')
      | ~ v3_funct_2('#skF_3',A_218,A_218)
      | ~ v1_funct_2('#skF_3',A_218,A_218)
      | ~ v1_funct_1('#skF_3')
      | A_218 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1853,c_2447])).

tff(c_2752,plain,(
    ! [A_316] :
      ( k2_funct_2(A_316,'#skF_3') = k2_funct_1('#skF_3')
      | ~ v3_funct_2('#skF_3',A_316,A_316)
      | ~ v1_funct_2('#skF_3',A_316,A_316)
      | A_316 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2453])).

tff(c_2755,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2752])).

tff(c_2758,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2755])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_funct_2(A_28,B_29),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2764,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2758,c_34])).

tff(c_2768,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1965,c_2764])).

tff(c_12,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2825,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2768,c_12])).

tff(c_1777,plain,(
    ! [A_148] :
      ( A_148 = '#skF_2'
      | k2_relat_1(A_148) != '#skF_1'
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1771,c_1770])).

tff(c_1801,plain,(
    ! [A_148] :
      ( A_148 = '#skF_3'
      | k2_relat_1(A_148) != '#skF_1'
      | ~ v1_relat_1(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_1777])).

tff(c_2838,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2825,c_1801])).

tff(c_2867,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2838])).

tff(c_14,plain,(
    ! [C_15,B_14,A_13] :
      ( v5_relat_1(C_15,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2824,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2768,c_14])).

tff(c_32,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(B_27) = A_26
      | ~ v2_funct_2(B_27,A_26)
      | ~ v5_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2853,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2824,c_32])).

tff(c_2856,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2825,c_2853])).

tff(c_2994,plain,(
    ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2867,c_2856])).

tff(c_2272,plain,(
    ! [A_261,B_262] :
      ( v1_funct_1(k2_funct_2(A_261,B_262))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k2_zfmisc_1(A_261,A_261)))
      | ~ v3_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2275,plain,(
    ! [A_218] :
      ( v1_funct_1(k2_funct_2(A_218,'#skF_3'))
      | ~ v3_funct_2('#skF_3',A_218,A_218)
      | ~ v1_funct_2('#skF_3',A_218,A_218)
      | ~ v1_funct_1('#skF_3')
      | A_218 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1853,c_2272])).

tff(c_2585,plain,(
    ! [A_299] :
      ( v1_funct_1(k2_funct_2(A_299,'#skF_3'))
      | ~ v3_funct_2('#skF_3',A_299,A_299)
      | ~ v1_funct_2('#skF_3',A_299,A_299)
      | A_299 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2275])).

tff(c_2587,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2585])).

tff(c_2590,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2587])).

tff(c_2759,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2758,c_2590])).

tff(c_26,plain,(
    ! [C_25,A_23,B_24] :
      ( v2_funct_1(C_25)
      | ~ v3_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2785,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2768,c_26])).

tff(c_2820,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2759,c_2785])).

tff(c_2868,plain,(
    ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2820])).

tff(c_2528,plain,(
    ! [A_288,B_289] :
      ( v3_funct_2(k2_funct_2(A_288,B_289),A_288,A_288)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(k2_zfmisc_1(A_288,A_288)))
      | ~ v3_funct_2(B_289,A_288,A_288)
      | ~ v1_funct_2(B_289,A_288,A_288)
      | ~ v1_funct_1(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2532,plain,(
    ! [A_218] :
      ( v3_funct_2(k2_funct_2(A_218,'#skF_3'),A_218,A_218)
      | ~ v3_funct_2('#skF_3',A_218,A_218)
      | ~ v1_funct_2('#skF_3',A_218,A_218)
      | ~ v1_funct_1('#skF_3')
      | A_218 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1853,c_2528])).

tff(c_2976,plain,(
    ! [A_334] :
      ( v3_funct_2(k2_funct_2(A_334,'#skF_3'),A_334,A_334)
      | ~ v3_funct_2('#skF_3',A_334,A_334)
      | ~ v1_funct_2('#skF_3',A_334,A_334)
      | A_334 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2532])).

tff(c_2979,plain,
    ( v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2758,c_2976])).

tff(c_2982,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2979])).

tff(c_2984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2868,c_2982])).

tff(c_2986,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2820])).

tff(c_24,plain,(
    ! [C_25,B_24,A_23] :
      ( v2_funct_2(C_25,B_24)
      | ~ v3_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2782,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2768,c_24])).

tff(c_2817,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2759,c_2782])).

tff(c_2996,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2986,c_2817])).

tff(c_2997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2994,c_2996])).

tff(c_2998,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2838])).

tff(c_1809,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_52])).

tff(c_2760,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2758,c_1809])).

tff(c_3006,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2998,c_2760])).

tff(c_3018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_3006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.02  
% 5.59/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.03  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.59/2.03  
% 5.59/2.03  %Foreground sorts:
% 5.59/2.03  
% 5.59/2.03  
% 5.59/2.03  %Background operators:
% 5.59/2.03  
% 5.59/2.03  
% 5.59/2.03  %Foreground operators:
% 5.59/2.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.59/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.59/2.03  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.59/2.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.59/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.59/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.59/2.03  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.59/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.59/2.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.59/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.59/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.59/2.03  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.59/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.59/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.59/2.03  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.59/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.59/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.59/2.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.59/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.59/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.59/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.59/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.59/2.03  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.59/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.59/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.59/2.03  
% 5.86/2.06  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.86/2.06  tff(f_170, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 5.86/2.06  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.86/2.06  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.86/2.06  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.86/2.06  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.86/2.06  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.86/2.06  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t197_relat_1)).
% 5.86/2.06  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.86/2.06  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.86/2.06  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.86/2.06  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.86/2.06  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.86/2.06  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.86/2.06  tff(f_107, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.86/2.06  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.86/2.06  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.86/2.06  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_103, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.86/2.06  tff(c_109, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_103])).
% 5.86/2.06  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_109])).
% 5.86/2.06  tff(c_139, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.86/2.06  tff(c_150, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_139])).
% 5.86/2.06  tff(c_174, plain, (![B_63, A_64]: (k2_relat_1(B_63)=A_64 | ~v2_funct_2(B_63, A_64) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.86/2.06  tff(c_183, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_150, c_174])).
% 5.86/2.06  tff(c_192, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_183])).
% 5.86/2.06  tff(c_683, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_192])).
% 5.86/2.06  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_929, plain, (![C_140, B_141, A_142]: (v2_funct_2(C_140, B_141) | ~v3_funct_2(C_140, A_142, B_141) | ~v1_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.06  tff(c_935, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_929])).
% 5.86/2.06  tff(c_943, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_935])).
% 5.86/2.06  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_683, c_943])).
% 5.86/2.06  tff(c_946, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_192])).
% 5.86/2.06  tff(c_958, plain, (![A_143, B_144, D_145]: (r2_relset_1(A_143, B_144, D_145, D_145) | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.86/2.06  tff(c_966, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_958])).
% 5.86/2.06  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_112, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_103])).
% 5.86/2.06  tff(c_121, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_112])).
% 5.86/2.06  tff(c_151, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_139])).
% 5.86/2.06  tff(c_180, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_151, c_174])).
% 5.86/2.06  tff(c_189, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_180])).
% 5.86/2.06  tff(c_193, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_189])).
% 5.86/2.06  tff(c_70, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_66, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_651, plain, (![C_110, B_111, A_112]: (v2_funct_2(C_110, B_111) | ~v3_funct_2(C_110, A_112, B_111) | ~v1_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.06  tff(c_660, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_651])).
% 5.86/2.06  tff(c_668, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_660])).
% 5.86/2.06  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_668])).
% 5.86/2.06  tff(c_671, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_189])).
% 5.86/2.06  tff(c_969, plain, (![B_147, A_148]: (B_147=A_148 | k2_relat_1(B_147)!=k1_xboole_0 | k2_relat_1(A_148)!=k1_xboole_0 | ~v1_relat_1(B_147) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.86/2.06  tff(c_973, plain, (![A_148]: (A_148='#skF_2' | k2_relat_1('#skF_2')!=k1_xboole_0 | k2_relat_1(A_148)!=k1_xboole_0 | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_121, c_969])).
% 5.86/2.06  tff(c_981, plain, (![A_148]: (A_148='#skF_2' | k1_xboole_0!='#skF_1' | k2_relat_1(A_148)!=k1_xboole_0 | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_671, c_973])).
% 5.86/2.06  tff(c_985, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_981])).
% 5.86/2.06  tff(c_68, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_986, plain, (![A_149, B_150, C_151]: (k2_relset_1(A_149, B_150, C_151)=k2_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.86/2.06  tff(c_995, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_986])).
% 5.86/2.06  tff(c_1001, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_671, c_995])).
% 5.86/2.06  tff(c_1143, plain, (![C_159, A_160, B_161]: (v2_funct_1(C_159) | ~v3_funct_2(C_159, A_160, B_161) | ~v1_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.06  tff(c_1152, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1143])).
% 5.86/2.06  tff(c_1159, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1152])).
% 5.86/2.06  tff(c_54, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_1737, plain, (![C_213, D_214, B_215, A_216]: (k2_funct_1(C_213)=D_214 | k1_xboole_0=B_215 | k1_xboole_0=A_216 | ~v2_funct_1(C_213) | ~r2_relset_1(A_216, A_216, k1_partfun1(A_216, B_215, B_215, A_216, C_213, D_214), k6_partfun1(A_216)) | k2_relset_1(A_216, B_215, C_213)!=B_215 | ~m1_subset_1(D_214, k1_zfmisc_1(k2_zfmisc_1(B_215, A_216))) | ~v1_funct_2(D_214, B_215, A_216) | ~v1_funct_1(D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))) | ~v1_funct_2(C_213, A_216, B_215) | ~v1_funct_1(C_213))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.86/2.06  tff(c_1746, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1737])).
% 5.86/2.06  tff(c_1749, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_60, c_56, c_1001, c_1159, c_1746])).
% 5.86/2.06  tff(c_1750, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_985, c_1749])).
% 5.86/2.06  tff(c_1405, plain, (![A_190, B_191]: (k2_funct_2(A_190, B_191)=k2_funct_1(B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.86/2.06  tff(c_1417, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1405])).
% 5.86/2.06  tff(c_1425, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1417])).
% 5.86/2.06  tff(c_52, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.86/2.06  tff(c_1432, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_52])).
% 5.86/2.06  tff(c_1758, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1750, c_1432])).
% 5.86/2.06  tff(c_1769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_966, c_1758])).
% 5.86/2.06  tff(c_1771, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_981])).
% 5.86/2.06  tff(c_1770, plain, (![A_148]: (A_148='#skF_2' | k2_relat_1(A_148)!=k1_xboole_0 | ~v1_relat_1(A_148))), inference(splitRight, [status(thm)], [c_981])).
% 5.86/2.06  tff(c_1778, plain, (![A_217]: (A_217='#skF_2' | k2_relat_1(A_217)!='#skF_1' | ~v1_relat_1(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_1771, c_1770])).
% 5.86/2.06  tff(c_1787, plain, ('#skF_2'='#skF_3' | k2_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_118, c_1778])).
% 5.86/2.06  tff(c_1799, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_946, c_1787])).
% 5.86/2.06  tff(c_48, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.86/2.06  tff(c_10, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.86/2.06  tff(c_71, plain, (![A_9]: (k2_relat_1(k6_partfun1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 5.86/2.06  tff(c_44, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.86/2.06  tff(c_106, plain, (![A_30]: (v1_relat_1(k6_partfun1(A_30)) | ~v1_relat_1(k2_zfmisc_1(A_30, A_30)))), inference(resolution, [status(thm)], [c_44, c_103])).
% 5.86/2.06  tff(c_115, plain, (![A_30]: (v1_relat_1(k6_partfun1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_106])).
% 5.86/2.06  tff(c_1781, plain, (![A_30]: (k6_partfun1(A_30)='#skF_2' | k2_relat_1(k6_partfun1(A_30))!='#skF_1')), inference(resolution, [status(thm)], [c_115, c_1778])).
% 5.86/2.06  tff(c_1792, plain, (![A_30]: (k6_partfun1(A_30)='#skF_2' | A_30!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1781])).
% 5.86/2.06  tff(c_1830, plain, (![A_218]: (k6_partfun1(A_218)='#skF_3' | A_218!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_1792])).
% 5.86/2.06  tff(c_1967, plain, (![A_232]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_232, A_232))) | A_232!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1830, c_44])).
% 5.86/2.06  tff(c_20, plain, (![A_19, B_20, D_22]: (r2_relset_1(A_19, B_20, D_22, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.86/2.06  tff(c_2022, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1967, c_20])).
% 5.86/2.06  tff(c_1965, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1830, c_44])).
% 5.86/2.06  tff(c_1853, plain, (![A_218]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_218, A_218))) | A_218!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1830, c_44])).
% 5.86/2.06  tff(c_2447, plain, (![A_274, B_275]: (k2_funct_2(A_274, B_275)=k2_funct_1(B_275) | ~m1_subset_1(B_275, k1_zfmisc_1(k2_zfmisc_1(A_274, A_274))) | ~v3_funct_2(B_275, A_274, A_274) | ~v1_funct_2(B_275, A_274, A_274) | ~v1_funct_1(B_275))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.86/2.06  tff(c_2453, plain, (![A_218]: (k2_funct_2(A_218, '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', A_218, A_218) | ~v1_funct_2('#skF_3', A_218, A_218) | ~v1_funct_1('#skF_3') | A_218!='#skF_1')), inference(resolution, [status(thm)], [c_1853, c_2447])).
% 5.86/2.06  tff(c_2752, plain, (![A_316]: (k2_funct_2(A_316, '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', A_316, A_316) | ~v1_funct_2('#skF_3', A_316, A_316) | A_316!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2453])).
% 5.86/2.06  tff(c_2755, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2752])).
% 5.86/2.06  tff(c_2758, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2755])).
% 5.86/2.06  tff(c_34, plain, (![A_28, B_29]: (m1_subset_1(k2_funct_2(A_28, B_29), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.86/2.06  tff(c_2764, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2758, c_34])).
% 5.86/2.06  tff(c_2768, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1965, c_2764])).
% 5.86/2.06  tff(c_12, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.86/2.06  tff(c_2825, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2768, c_12])).
% 5.86/2.06  tff(c_1777, plain, (![A_148]: (A_148='#skF_2' | k2_relat_1(A_148)!='#skF_1' | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_1771, c_1770])).
% 5.86/2.06  tff(c_1801, plain, (![A_148]: (A_148='#skF_3' | k2_relat_1(A_148)!='#skF_1' | ~v1_relat_1(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_1777])).
% 5.86/2.06  tff(c_2838, plain, (k2_funct_1('#skF_3')='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(resolution, [status(thm)], [c_2825, c_1801])).
% 5.86/2.06  tff(c_2867, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_2838])).
% 5.86/2.06  tff(c_14, plain, (![C_15, B_14, A_13]: (v5_relat_1(C_15, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.86/2.06  tff(c_2824, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2768, c_14])).
% 5.86/2.06  tff(c_32, plain, (![B_27, A_26]: (k2_relat_1(B_27)=A_26 | ~v2_funct_2(B_27, A_26) | ~v5_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.86/2.06  tff(c_2853, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2824, c_32])).
% 5.86/2.06  tff(c_2856, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2825, c_2853])).
% 5.86/2.06  tff(c_2994, plain, (~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2867, c_2856])).
% 5.86/2.06  tff(c_2272, plain, (![A_261, B_262]: (v1_funct_1(k2_funct_2(A_261, B_262)) | ~m1_subset_1(B_262, k1_zfmisc_1(k2_zfmisc_1(A_261, A_261))) | ~v3_funct_2(B_262, A_261, A_261) | ~v1_funct_2(B_262, A_261, A_261) | ~v1_funct_1(B_262))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.86/2.06  tff(c_2275, plain, (![A_218]: (v1_funct_1(k2_funct_2(A_218, '#skF_3')) | ~v3_funct_2('#skF_3', A_218, A_218) | ~v1_funct_2('#skF_3', A_218, A_218) | ~v1_funct_1('#skF_3') | A_218!='#skF_1')), inference(resolution, [status(thm)], [c_1853, c_2272])).
% 5.86/2.06  tff(c_2585, plain, (![A_299]: (v1_funct_1(k2_funct_2(A_299, '#skF_3')) | ~v3_funct_2('#skF_3', A_299, A_299) | ~v1_funct_2('#skF_3', A_299, A_299) | A_299!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2275])).
% 5.86/2.06  tff(c_2587, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2585])).
% 5.86/2.06  tff(c_2590, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2587])).
% 5.86/2.06  tff(c_2759, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2758, c_2590])).
% 5.86/2.06  tff(c_26, plain, (![C_25, A_23, B_24]: (v2_funct_1(C_25) | ~v3_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.06  tff(c_2785, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2768, c_26])).
% 5.86/2.06  tff(c_2820, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2759, c_2785])).
% 5.86/2.06  tff(c_2868, plain, (~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2820])).
% 5.86/2.06  tff(c_2528, plain, (![A_288, B_289]: (v3_funct_2(k2_funct_2(A_288, B_289), A_288, A_288) | ~m1_subset_1(B_289, k1_zfmisc_1(k2_zfmisc_1(A_288, A_288))) | ~v3_funct_2(B_289, A_288, A_288) | ~v1_funct_2(B_289, A_288, A_288) | ~v1_funct_1(B_289))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.86/2.06  tff(c_2532, plain, (![A_218]: (v3_funct_2(k2_funct_2(A_218, '#skF_3'), A_218, A_218) | ~v3_funct_2('#skF_3', A_218, A_218) | ~v1_funct_2('#skF_3', A_218, A_218) | ~v1_funct_1('#skF_3') | A_218!='#skF_1')), inference(resolution, [status(thm)], [c_1853, c_2528])).
% 5.86/2.06  tff(c_2976, plain, (![A_334]: (v3_funct_2(k2_funct_2(A_334, '#skF_3'), A_334, A_334) | ~v3_funct_2('#skF_3', A_334, A_334) | ~v1_funct_2('#skF_3', A_334, A_334) | A_334!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2532])).
% 5.86/2.06  tff(c_2979, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2758, c_2976])).
% 5.86/2.06  tff(c_2982, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2979])).
% 5.86/2.06  tff(c_2984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2868, c_2982])).
% 5.86/2.06  tff(c_2986, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2820])).
% 5.86/2.06  tff(c_24, plain, (![C_25, B_24, A_23]: (v2_funct_2(C_25, B_24) | ~v3_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.86/2.06  tff(c_2782, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2768, c_24])).
% 5.86/2.06  tff(c_2817, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2759, c_2782])).
% 5.86/2.06  tff(c_2996, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2986, c_2817])).
% 5.86/2.06  tff(c_2997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2994, c_2996])).
% 5.86/2.06  tff(c_2998, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2838])).
% 5.86/2.06  tff(c_1809, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_52])).
% 5.86/2.06  tff(c_2760, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2758, c_1809])).
% 5.86/2.06  tff(c_3006, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2998, c_2760])).
% 5.86/2.06  tff(c_3018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2022, c_3006])).
% 5.86/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.06  
% 5.86/2.06  Inference rules
% 5.86/2.06  ----------------------
% 5.86/2.06  #Ref     : 10
% 5.86/2.06  #Sup     : 700
% 5.86/2.06  #Fact    : 0
% 5.86/2.06  #Define  : 0
% 5.86/2.06  #Split   : 17
% 5.86/2.06  #Chain   : 0
% 5.86/2.06  #Close   : 0
% 5.86/2.06  
% 5.86/2.06  Ordering : KBO
% 5.86/2.06  
% 5.86/2.06  Simplification rules
% 5.86/2.06  ----------------------
% 5.86/2.06  #Subsume      : 256
% 5.86/2.06  #Demod        : 392
% 5.86/2.06  #Tautology    : 171
% 5.86/2.06  #SimpNegUnit  : 10
% 5.86/2.06  #BackRed      : 39
% 5.86/2.06  
% 5.86/2.06  #Partial instantiations: 0
% 5.86/2.06  #Strategies tried      : 1
% 5.86/2.06  
% 5.86/2.06  Timing (in seconds)
% 5.86/2.06  ----------------------
% 5.86/2.06  Preprocessing        : 0.37
% 5.86/2.06  Parsing              : 0.19
% 5.86/2.06  CNF conversion       : 0.02
% 5.86/2.06  Main loop            : 0.90
% 5.86/2.06  Inferencing          : 0.30
% 5.86/2.06  Reduction            : 0.33
% 5.86/2.06  Demodulation         : 0.24
% 5.86/2.06  BG Simplification    : 0.04
% 5.86/2.06  Subsumption          : 0.17
% 5.86/2.06  Abstraction          : 0.04
% 5.86/2.06  MUC search           : 0.00
% 5.86/2.06  Cooper               : 0.00
% 5.86/2.06  Total                : 1.33
% 5.86/2.06  Index Insertion      : 0.00
% 5.86/2.06  Index Deletion       : 0.00
% 5.86/2.06  Index Matching       : 0.00
% 5.86/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
