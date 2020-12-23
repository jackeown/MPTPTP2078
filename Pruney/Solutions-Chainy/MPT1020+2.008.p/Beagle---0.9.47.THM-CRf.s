%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:51 EST 2020

% Result     : Theorem 56.25s
% Output     : CNFRefutation 56.63s
% Verified   : 
% Statistics : Number of formulae       :  310 (10311 expanded)
%              Number of leaves         :   48 (3341 expanded)
%              Depth                    :   20
%              Number of atoms          :  692 (31062 expanded)
%              Number of equality atoms :  167 (7698 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_216,negated_conjecture,(
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_135,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_139,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_178,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_194,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_106,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_106])).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_118,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_106])).

tff(c_200,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_relset_1(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_208,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_200])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_183,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_194,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_183])).

tff(c_210,plain,(
    ! [B_84,A_85] :
      ( k2_relat_1(B_84) = A_85
      | ~ v2_funct_2(B_84,A_85)
      | ~ v5_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_219,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_210])).

tff(c_228,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_219])).

tff(c_371,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_70,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_413,plain,(
    ! [C_113,B_114,A_115] :
      ( v2_funct_2(C_113,B_114)
      | ~ v3_funct_2(C_113,A_115,B_114)
      | ~ v1_funct_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_419,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_413])).

tff(c_426,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_419])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_426])).

tff(c_429,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_82,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_78,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_466,plain,(
    ! [C_120,A_121,B_122] :
      ( v2_funct_1(C_120)
      | ~ v3_funct_2(C_120,A_121,B_122)
      | ~ v1_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_475,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_466])).

tff(c_482,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_475])).

tff(c_195,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_183])).

tff(c_216,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_195,c_210])).

tff(c_225,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_216])).

tff(c_229,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_340,plain,(
    ! [C_103,B_104,A_105] :
      ( v2_funct_2(C_103,B_104)
      | ~ v3_funct_2(C_103,A_105,B_104)
      | ~ v1_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_349,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_340])).

tff(c_356,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_349])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_356])).

tff(c_359,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_56,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1572,plain,(
    ! [A_212,B_213] :
      ( k2_funct_1(A_212) = B_213
      | k6_partfun1(k2_relat_1(A_212)) != k5_relat_1(B_213,A_212)
      | k2_relat_1(B_213) != k1_relat_1(A_212)
      | ~ v2_funct_1(A_212)
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_1578,plain,(
    ! [B_213] :
      ( k2_funct_1('#skF_2') = B_213
      | k5_relat_1(B_213,'#skF_2') != k6_partfun1('#skF_1')
      | k2_relat_1(B_213) != k1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1572])).

tff(c_1633,plain,(
    ! [B_228] :
      ( k2_funct_1('#skF_2') = B_228
      | k5_relat_1(B_228,'#skF_2') != k6_partfun1('#skF_1')
      | k2_relat_1(B_228) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(B_228)
      | ~ v1_relat_1(B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_482,c_1578])).

tff(c_1642,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_1633])).

tff(c_1652,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_429,c_1642])).

tff(c_1806,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1652])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1513,plain,(
    ! [A_203,B_204] :
      ( k2_funct_2(A_203,B_204) = k2_funct_1(B_204)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(k2_zfmisc_1(A_203,A_203)))
      | ~ v3_funct_2(B_204,A_203,A_203)
      | ~ v1_funct_2(B_204,A_203,A_203)
      | ~ v1_funct_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1522,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1513])).

tff(c_1529,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1522])).

tff(c_1654,plain,(
    ! [A_229,B_230] :
      ( m1_subset_1(k2_funct_2(A_229,B_230),k1_zfmisc_1(k2_zfmisc_1(A_229,A_229)))
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_229,A_229)))
      | ~ v3_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_1(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1695,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_1654])).

tff(c_1716,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_1695])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1753,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1716,c_2])).

tff(c_1789,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1753])).

tff(c_526,plain,(
    ! [A_132,B_133] :
      ( v1_funct_1(k2_funct_2(A_132,B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_132,A_132)))
      | ~ v3_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_2(B_133,A_132,A_132)
      | ~ v1_funct_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_535,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_526])).

tff(c_542,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_535])).

tff(c_1535,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_542])).

tff(c_1541,plain,(
    ! [A_205,B_206] :
      ( v3_funct_2(k2_funct_2(A_205,B_206),A_205,A_205)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1547,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1541])).

tff(c_1554,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_1529,c_1547])).

tff(c_26,plain,(
    ! [C_23,B_22,A_21] :
      ( v2_funct_2(C_23,B_22)
      | ~ v3_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1739,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1716,c_26])).

tff(c_1780,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1554,c_1739])).

tff(c_18,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1785,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1716,c_18])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(B_25) = A_24
      | ~ v2_funct_2(B_25,A_24)
      | ~ v5_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1810,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1785,c_34])).

tff(c_1813,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_1780,c_1810])).

tff(c_10,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1844,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1813,c_10])).

tff(c_1858,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_82,c_482,c_1844])).

tff(c_1860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1806,c_1858])).

tff(c_1861,plain,
    ( k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1652])).

tff(c_63758,plain,(
    k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1861])).

tff(c_1431,plain,(
    ! [C_200,F_199,D_196,E_201,A_198,B_197] :
      ( m1_subset_1(k1_partfun1(A_198,B_197,C_200,D_196,E_201,F_199),k1_zfmisc_1(k2_zfmisc_1(A_198,D_196)))
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_200,D_196)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197)))
      | ~ v1_funct_1(E_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_502,plain,(
    ! [D_128,C_129,A_130,B_131] :
      ( D_128 = C_129
      | ~ r2_relset_1(A_130,B_131,C_129,D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_510,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_502])).

tff(c_525,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_510])).

tff(c_544,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_1461,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1431,c_544])).

tff(c_1499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_76,c_74,c_68,c_1461])).

tff(c_1500,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_1879,plain,(
    ! [F_238,B_242,A_237,C_239,E_240,D_241] :
      ( k1_partfun1(A_237,B_242,C_239,D_241,E_240,F_238) = k5_relat_1(E_240,F_238)
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(C_239,D_241)))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_237,B_242)))
      | ~ v1_funct_1(E_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1887,plain,(
    ! [A_237,B_242,E_240] :
      ( k1_partfun1(A_237,B_242,'#skF_1','#skF_1',E_240,'#skF_3') = k5_relat_1(E_240,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_237,B_242)))
      | ~ v1_funct_1(E_240) ) ),
    inference(resolution,[status(thm)],[c_68,c_1879])).

tff(c_1986,plain,(
    ! [A_243,B_244,E_245] :
      ( k1_partfun1(A_243,B_244,'#skF_1','#skF_1',E_245,'#skF_3') = k5_relat_1(E_245,'#skF_3')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(E_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1887])).

tff(c_2004,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1986])).

tff(c_2018,plain,(
    k5_relat_1('#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1500,c_2004])).

tff(c_472,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_466])).

tff(c_479,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_472])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1519,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1513])).

tff(c_1526,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1519])).

tff(c_532,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_526])).

tff(c_539,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_532])).

tff(c_1530,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1526,c_539])).

tff(c_1545,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1541])).

tff(c_1551,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1526,c_1545])).

tff(c_1698,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1526,c_1654])).

tff(c_1718,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_1698])).

tff(c_1923,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1718,c_26])).

tff(c_1967,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1530,c_1551,c_1923])).

tff(c_1937,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1718,c_2])).

tff(c_1976,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1937])).

tff(c_1972,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1718,c_18])).

tff(c_2022,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1972,c_34])).

tff(c_2025,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_2022])).

tff(c_63958,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1967,c_2025])).

tff(c_63968,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_63958,c_10])).

tff(c_63982,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_74,c_479,c_63968])).

tff(c_1576,plain,(
    ! [B_213] :
      ( k2_funct_1('#skF_3') = B_213
      | k5_relat_1(B_213,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_213) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_1572])).

tff(c_1580,plain,(
    ! [B_213] :
      ( k2_funct_1('#skF_3') = B_213
      | k5_relat_1(B_213,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_213) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_74,c_479,c_1576])).

tff(c_88650,plain,(
    ! [B_1429] :
      ( k2_funct_1('#skF_3') = B_1429
      | k5_relat_1(B_1429,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1429) != '#skF_1'
      | ~ v1_funct_1(B_1429)
      | ~ v1_relat_1(B_1429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63982,c_1580])).

tff(c_88938,plain,
    ( k2_funct_1('#skF_3') = '#skF_2'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_2') != '#skF_1'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_88650])).

tff(c_89167,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_359,c_2018,c_88938])).

tff(c_207,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_50,c_200])).

tff(c_2395,plain,(
    ! [A_261,B_262,C_263,D_264] :
      ( k2_relset_1(A_261,B_262,C_263) = B_262
      | ~ r2_relset_1(B_262,B_262,k1_partfun1(B_262,A_261,A_261,B_262,D_264,C_263),k6_partfun1(B_262))
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(B_262,A_261)))
      | ~ v1_funct_2(D_264,B_262,A_261)
      | ~ v1_funct_1(D_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2(C_263,A_261,B_262)
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2404,plain,
    ( k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_2395])).

tff(c_2410,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_82,c_80,c_76,c_207,c_2404])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_144,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_361,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_144])).

tff(c_2030,plain,(
    ! [A_246,C_247,B_248] :
      ( k6_partfun1(A_246) = k5_relat_1(C_247,k2_funct_1(C_247))
      | k1_xboole_0 = B_248
      | ~ v2_funct_1(C_247)
      | k2_relset_1(A_246,B_248,C_247) != B_248
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_246,B_248)))
      | ~ v1_funct_2(C_247,A_246,B_248)
      | ~ v1_funct_1(C_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_2040,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2030])).

tff(c_2055,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_479,c_2040])).

tff(c_2056,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_2055])).

tff(c_63753,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2410,c_2056])).

tff(c_89293,plain,(
    k5_relat_1('#skF_3','#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89167,c_63753])).

tff(c_89395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63758,c_89293])).

tff(c_89396,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1861])).

tff(c_64,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1536,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_64])).

tff(c_89415,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89396,c_1536])).

tff(c_89435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_89415])).

tff(c_89436,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_89437,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_89445,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89436,c_89437])).

tff(c_89513,plain,(
    ! [C_1435,B_1436,A_1437] :
      ( v5_relat_1(C_1435,B_1436)
      | ~ m1_subset_1(C_1435,k1_zfmisc_1(k2_zfmisc_1(A_1437,B_1436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_89525,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_89513])).

tff(c_89805,plain,(
    ! [B_1487,A_1488] :
      ( k2_relat_1(B_1487) = A_1488
      | ~ v2_funct_2(B_1487,A_1488)
      | ~ v5_relat_1(B_1487,A_1488)
      | ~ v1_relat_1(B_1487) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_89814,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_89525,c_89805])).

tff(c_89826,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_89445,c_89814])).

tff(c_89830,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_89826])).

tff(c_89917,plain,(
    ! [C_1504,B_1505,A_1506] :
      ( v2_funct_2(C_1504,B_1505)
      | ~ v3_funct_2(C_1504,A_1506,B_1505)
      | ~ v1_funct_1(C_1504)
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(k2_zfmisc_1(A_1506,B_1505))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_89926,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_89917])).

tff(c_89933,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_89926])).

tff(c_89935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89830,c_89933])).

tff(c_89936,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_89826])).

tff(c_126,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_117,c_6])).

tff(c_89452,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89436,c_89436,c_126])).

tff(c_89453,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_89452])).

tff(c_89949,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89936,c_89453])).

tff(c_89524,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_89513])).

tff(c_89817,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89524,c_89805])).

tff(c_89829,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_89817])).

tff(c_90006,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_89949,c_89829])).

tff(c_90040,plain,(
    ! [C_1511,B_1512,A_1513] :
      ( v2_funct_2(C_1511,B_1512)
      | ~ v3_funct_2(C_1511,A_1513,B_1512)
      | ~ v1_funct_1(C_1511)
      | ~ m1_subset_1(C_1511,k1_zfmisc_1(k2_zfmisc_1(A_1513,B_1512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_90049,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_90040])).

tff(c_90056,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_90049])).

tff(c_90058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90006,c_90056])).

tff(c_90059,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_89452])).

tff(c_90060,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_89452])).

tff(c_90084,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90059,c_90060])).

tff(c_90148,plain,(
    ! [C_1524,B_1525,A_1526] :
      ( v5_relat_1(C_1524,B_1525)
      | ~ m1_subset_1(C_1524,k1_zfmisc_1(k2_zfmisc_1(A_1526,B_1525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90156,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_90148])).

tff(c_90333,plain,(
    ! [B_1559,A_1560] :
      ( k2_relat_1(B_1559) = A_1560
      | ~ v2_funct_2(B_1559,A_1560)
      | ~ v5_relat_1(B_1559,A_1560)
      | ~ v1_relat_1(B_1559) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_90342,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90156,c_90333])).

tff(c_90351,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90084,c_90342])).

tff(c_90352,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_90351])).

tff(c_90374,plain,(
    ! [C_1570,B_1571,A_1572] :
      ( v2_funct_2(C_1570,B_1571)
      | ~ v3_funct_2(C_1570,A_1572,B_1571)
      | ~ v1_funct_1(C_1570)
      | ~ m1_subset_1(C_1570,k1_zfmisc_1(k2_zfmisc_1(A_1572,B_1571))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_90380,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_90374])).

tff(c_90384,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_90380])).

tff(c_90386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90352,c_90384])).

tff(c_90387,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_90351])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_117,c_8])).

tff(c_89450,plain,
    ( k1_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89436,c_89436,c_125])).

tff(c_89451,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_89450])).

tff(c_90061,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90059,c_89451])).

tff(c_90400,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90387,c_90387,c_90061])).

tff(c_90405,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90387,c_117])).

tff(c_90409,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90387,c_74])).

tff(c_90408,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90387,c_70])).

tff(c_90406,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90387,c_68])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( v2_funct_1(C_23)
      | ~ v3_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_90451,plain,
    ( v2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90406,c_28])).

tff(c_90468,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90409,c_90408,c_90451])).

tff(c_90407,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90387,c_72])).

tff(c_90564,plain,(
    ! [A_1602,B_1603] :
      ( k2_funct_2(A_1602,B_1603) = k2_funct_1(B_1603)
      | ~ m1_subset_1(B_1603,k1_zfmisc_1(k2_zfmisc_1(A_1602,A_1602)))
      | ~ v3_funct_2(B_1603,A_1602,A_1602)
      | ~ v1_funct_2(B_1603,A_1602,A_1602)
      | ~ v1_funct_1(B_1603) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_90567,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90406,c_90564])).

tff(c_90573,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90409,c_90407,c_90408,c_90567])).

tff(c_90609,plain,(
    ! [A_1613,B_1614] :
      ( m1_subset_1(k2_funct_2(A_1613,B_1614),k1_zfmisc_1(k2_zfmisc_1(A_1613,A_1613)))
      | ~ m1_subset_1(B_1614,k1_zfmisc_1(k2_zfmisc_1(A_1613,A_1613)))
      | ~ v3_funct_2(B_1614,A_1613,A_1613)
      | ~ v1_funct_2(B_1614,A_1613,A_1613)
      | ~ v1_funct_1(B_1614) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_90642,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90573,c_90609])).

tff(c_90657,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90409,c_90407,c_90408,c_90406,c_90642])).

tff(c_90684,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_90657,c_2])).

tff(c_90711,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90684])).

tff(c_90547,plain,(
    ! [A_1598,B_1599] :
      ( v1_funct_1(k2_funct_2(A_1598,B_1599))
      | ~ m1_subset_1(B_1599,k1_zfmisc_1(k2_zfmisc_1(A_1598,A_1598)))
      | ~ v3_funct_2(B_1599,A_1598,A_1598)
      | ~ v1_funct_2(B_1599,A_1598,A_1598)
      | ~ v1_funct_1(B_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_90550,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90406,c_90547])).

tff(c_90556,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90409,c_90407,c_90408,c_90550])).

tff(c_90575,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90573,c_90556])).

tff(c_90581,plain,(
    ! [A_1604,B_1605] :
      ( v3_funct_2(k2_funct_2(A_1604,B_1605),A_1604,A_1604)
      | ~ m1_subset_1(B_1605,k1_zfmisc_1(k2_zfmisc_1(A_1604,A_1604)))
      | ~ v3_funct_2(B_1605,A_1604,A_1604)
      | ~ v1_funct_2(B_1605,A_1604,A_1604)
      | ~ v1_funct_1(B_1605) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_90583,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_90406,c_90581])).

tff(c_90588,plain,(
    v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90409,c_90407,c_90408,c_90573,c_90583])).

tff(c_90670,plain,
    ( v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_90657,c_26])).

tff(c_90702,plain,(
    v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90575,c_90588,c_90670])).

tff(c_90707,plain,(
    v5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_90657,c_18])).

tff(c_90724,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_90707,c_34])).

tff(c_90727,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90711,c_90702,c_90724])).

tff(c_90736,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90727,c_10])).

tff(c_90750,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90405,c_90409,c_90468,c_90736])).

tff(c_90752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90400,c_90750])).

tff(c_90753,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_89450])).

tff(c_90755,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90753,c_90753,c_89445])).

tff(c_90839,plain,(
    ! [C_1621,B_1622,A_1623] :
      ( v5_relat_1(C_1621,B_1622)
      | ~ m1_subset_1(C_1621,k1_zfmisc_1(k2_zfmisc_1(A_1623,B_1622))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_90847,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_90839])).

tff(c_91009,plain,(
    ! [B_1651,A_1652] :
      ( k2_relat_1(B_1651) = A_1652
      | ~ v2_funct_2(B_1651,A_1652)
      | ~ v5_relat_1(B_1651,A_1652)
      | ~ v1_relat_1(B_1651) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_91015,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90847,c_91009])).

tff(c_91021,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_90755,c_91015])).

tff(c_91028,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_91021])).

tff(c_91070,plain,(
    ! [C_1663,B_1664,A_1665] :
      ( v2_funct_2(C_1663,B_1664)
      | ~ v3_funct_2(C_1663,A_1665,B_1664)
      | ~ v1_funct_1(C_1663)
      | ~ m1_subset_1(C_1663,k1_zfmisc_1(k2_zfmisc_1(A_1665,B_1664))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_91076,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_91070])).

tff(c_91080,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_91076])).

tff(c_91082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91028,c_91080])).

tff(c_91083,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_91021])).

tff(c_91101,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91083,c_68])).

tff(c_91218,plain,(
    ! [A_1672,B_1673,D_1674] :
      ( r2_relset_1(A_1672,B_1673,D_1674,D_1674)
      | ~ m1_subset_1(D_1674,k1_zfmisc_1(k2_zfmisc_1(A_1672,B_1673))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_91223,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_91101,c_91218])).

tff(c_91104,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91083,c_74])).

tff(c_91102,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91083,c_72])).

tff(c_91103,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91083,c_70])).

tff(c_91288,plain,(
    ! [A_1697,B_1698] :
      ( k2_funct_2(A_1697,B_1698) = k2_funct_1(B_1698)
      | ~ m1_subset_1(B_1698,k1_zfmisc_1(k2_zfmisc_1(A_1697,A_1697)))
      | ~ v3_funct_2(B_1698,A_1697,A_1697)
      | ~ v1_funct_2(B_1698,A_1697,A_1697)
      | ~ v1_funct_1(B_1698) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_91291,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_91101,c_91288])).

tff(c_91297,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91104,c_91102,c_91103,c_91291])).

tff(c_91371,plain,(
    ! [A_1721,B_1722] :
      ( m1_subset_1(k2_funct_2(A_1721,B_1722),k1_zfmisc_1(k2_zfmisc_1(A_1721,A_1721)))
      | ~ m1_subset_1(B_1722,k1_zfmisc_1(k2_zfmisc_1(A_1721,A_1721)))
      | ~ v3_funct_2(B_1722,A_1721,A_1721)
      | ~ v1_funct_2(B_1722,A_1721,A_1721)
      | ~ v1_funct_1(B_1722) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_91409,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_91297,c_91371])).

tff(c_91426,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91104,c_91102,c_91103,c_91101,c_91409])).

tff(c_91458,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_91426,c_2])).

tff(c_91491,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_91458])).

tff(c_91272,plain,(
    ! [A_1693,B_1694] :
      ( v1_funct_1(k2_funct_2(A_1693,B_1694))
      | ~ m1_subset_1(B_1694,k1_zfmisc_1(k2_zfmisc_1(A_1693,A_1693)))
      | ~ v3_funct_2(B_1694,A_1693,A_1693)
      | ~ v1_funct_2(B_1694,A_1693,A_1693)
      | ~ v1_funct_1(B_1694) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_91275,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_91101,c_91272])).

tff(c_91281,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91104,c_91102,c_91103,c_91275])).

tff(c_91299,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91297,c_91281])).

tff(c_91316,plain,(
    ! [A_1703,B_1704] :
      ( v3_funct_2(k2_funct_2(A_1703,B_1704),A_1703,A_1703)
      | ~ m1_subset_1(B_1704,k1_zfmisc_1(k2_zfmisc_1(A_1703,A_1703)))
      | ~ v3_funct_2(B_1704,A_1703,A_1703)
      | ~ v1_funct_2(B_1704,A_1703,A_1703)
      | ~ v1_funct_1(B_1704) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_91318,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_91101,c_91316])).

tff(c_91323,plain,(
    v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91104,c_91102,c_91103,c_91297,c_91318])).

tff(c_91444,plain,
    ( v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_91426,c_26])).

tff(c_91482,plain,(
    v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91299,c_91323,c_91444])).

tff(c_91488,plain,(
    v5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_91426,c_18])).

tff(c_91512,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_91488,c_34])).

tff(c_91515,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91491,c_91482,c_91512])).

tff(c_89439,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != '#skF_2'
      | A_6 = '#skF_2'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89436,c_89436,c_6])).

tff(c_90803,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != '#skF_3'
      | A_6 = '#skF_3'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90753,c_90753,c_89439])).

tff(c_91093,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != '#skF_1'
      | A_6 = '#skF_1'
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91083,c_91083,c_90803])).

tff(c_91507,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_91491,c_91093])).

tff(c_91601,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91515,c_91507])).

tff(c_90759,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90753,c_64])).

tff(c_91095,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91083,c_91083,c_90759])).

tff(c_91300,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91297,c_91095])).

tff(c_91619,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91601,c_91300])).

tff(c_91637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91223,c_91619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.25/43.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.25/43.67  
% 56.25/43.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.57/43.67  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 56.57/43.67  
% 56.57/43.67  %Foreground sorts:
% 56.57/43.67  
% 56.57/43.67  
% 56.57/43.67  %Background operators:
% 56.57/43.67  
% 56.57/43.67  
% 56.57/43.67  %Foreground operators:
% 56.57/43.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 56.57/43.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 56.57/43.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 56.57/43.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 56.57/43.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.57/43.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 56.57/43.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 56.57/43.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 56.57/43.67  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 56.57/43.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 56.57/43.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 56.57/43.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 56.57/43.67  tff('#skF_2', type, '#skF_2': $i).
% 56.57/43.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 56.57/43.67  tff('#skF_3', type, '#skF_3': $i).
% 56.57/43.67  tff('#skF_1', type, '#skF_1': $i).
% 56.57/43.67  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 56.57/43.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 56.57/43.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 56.57/43.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 56.57/43.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.57/43.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 56.57/43.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 56.57/43.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 56.57/43.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.57/43.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 56.57/43.67  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 56.57/43.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 56.57/43.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 56.57/43.67  
% 56.63/43.71  tff(f_216, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 56.63/43.71  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 56.63/43.71  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 56.63/43.71  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 56.63/43.71  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 56.63/43.71  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 56.63/43.71  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 56.63/43.71  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 56.63/43.71  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 56.63/43.71  tff(f_159, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 56.63/43.71  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 56.63/43.71  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 56.63/43.71  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 56.63/43.71  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 56.63/43.71  tff(f_139, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 56.63/43.71  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 56.63/43.71  tff(f_178, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 56.63/43.71  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 56.63/43.71  tff(f_194, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 56.63/43.71  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_106, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 56.63/43.71  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_106])).
% 56.63/43.71  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_118, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_106])).
% 56.63/43.71  tff(c_200, plain, (![A_81, B_82, D_83]: (r2_relset_1(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 56.63/43.71  tff(c_208, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_200])).
% 56.63/43.71  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_183, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.63/43.71  tff(c_194, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_183])).
% 56.63/43.71  tff(c_210, plain, (![B_84, A_85]: (k2_relat_1(B_84)=A_85 | ~v2_funct_2(B_84, A_85) | ~v5_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.63/43.71  tff(c_219, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_194, c_210])).
% 56.63/43.71  tff(c_228, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_219])).
% 56.63/43.71  tff(c_371, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_228])).
% 56.63/43.71  tff(c_70, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_413, plain, (![C_113, B_114, A_115]: (v2_funct_2(C_113, B_114) | ~v3_funct_2(C_113, A_115, B_114) | ~v1_funct_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_419, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_413])).
% 56.63/43.71  tff(c_426, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_419])).
% 56.63/43.71  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_426])).
% 56.63/43.71  tff(c_429, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_228])).
% 56.63/43.71  tff(c_82, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_78, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_466, plain, (![C_120, A_121, B_122]: (v2_funct_1(C_120) | ~v3_funct_2(C_120, A_121, B_122) | ~v1_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_475, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_466])).
% 56.63/43.71  tff(c_482, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_475])).
% 56.63/43.71  tff(c_195, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_183])).
% 56.63/43.71  tff(c_216, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_195, c_210])).
% 56.63/43.71  tff(c_225, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_216])).
% 56.63/43.71  tff(c_229, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_225])).
% 56.63/43.71  tff(c_340, plain, (![C_103, B_104, A_105]: (v2_funct_2(C_103, B_104) | ~v3_funct_2(C_103, A_105, B_104) | ~v1_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_349, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_340])).
% 56.63/43.71  tff(c_356, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_349])).
% 56.63/43.71  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_356])).
% 56.63/43.71  tff(c_359, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_225])).
% 56.63/43.71  tff(c_56, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.63/43.71  tff(c_14, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 56.63/43.71  tff(c_1572, plain, (![A_212, B_213]: (k2_funct_1(A_212)=B_213 | k6_partfun1(k2_relat_1(A_212))!=k5_relat_1(B_213, A_212) | k2_relat_1(B_213)!=k1_relat_1(A_212) | ~v2_funct_1(A_212) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14])).
% 56.63/43.71  tff(c_1578, plain, (![B_213]: (k2_funct_1('#skF_2')=B_213 | k5_relat_1(B_213, '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1(B_213)!=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_1572])).
% 56.63/43.71  tff(c_1633, plain, (![B_228]: (k2_funct_1('#skF_2')=B_228 | k5_relat_1(B_228, '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1(B_228)!=k1_relat_1('#skF_2') | ~v1_funct_1(B_228) | ~v1_relat_1(B_228))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_482, c_1578])).
% 56.63/43.71  tff(c_1642, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_1633])).
% 56.63/43.71  tff(c_1652, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_429, c_1642])).
% 56.63/43.71  tff(c_1806, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1652])).
% 56.63/43.71  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 56.63/43.71  tff(c_80, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_1513, plain, (![A_203, B_204]: (k2_funct_2(A_203, B_204)=k2_funct_1(B_204) | ~m1_subset_1(B_204, k1_zfmisc_1(k2_zfmisc_1(A_203, A_203))) | ~v3_funct_2(B_204, A_203, A_203) | ~v1_funct_2(B_204, A_203, A_203) | ~v1_funct_1(B_204))), inference(cnfTransformation, [status(thm)], [f_159])).
% 56.63/43.71  tff(c_1522, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1513])).
% 56.63/43.71  tff(c_1529, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1522])).
% 56.63/43.71  tff(c_1654, plain, (![A_229, B_230]: (m1_subset_1(k2_funct_2(A_229, B_230), k1_zfmisc_1(k2_zfmisc_1(A_229, A_229))) | ~m1_subset_1(B_230, k1_zfmisc_1(k2_zfmisc_1(A_229, A_229))) | ~v3_funct_2(B_230, A_229, A_229) | ~v1_funct_2(B_230, A_229, A_229) | ~v1_funct_1(B_230))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_1695, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1529, c_1654])).
% 56.63/43.71  tff(c_1716, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_1695])).
% 56.63/43.71  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 56.63/43.71  tff(c_1753, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1716, c_2])).
% 56.63/43.71  tff(c_1789, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1753])).
% 56.63/43.71  tff(c_526, plain, (![A_132, B_133]: (v1_funct_1(k2_funct_2(A_132, B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_132, A_132))) | ~v3_funct_2(B_133, A_132, A_132) | ~v1_funct_2(B_133, A_132, A_132) | ~v1_funct_1(B_133))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_535, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_526])).
% 56.63/43.71  tff(c_542, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_535])).
% 56.63/43.71  tff(c_1535, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_542])).
% 56.63/43.71  tff(c_1541, plain, (![A_205, B_206]: (v3_funct_2(k2_funct_2(A_205, B_206), A_205, A_205) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_1547, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1541])).
% 56.63/43.71  tff(c_1554, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_1529, c_1547])).
% 56.63/43.71  tff(c_26, plain, (![C_23, B_22, A_21]: (v2_funct_2(C_23, B_22) | ~v3_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_1739, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1716, c_26])).
% 56.63/43.71  tff(c_1780, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1554, c_1739])).
% 56.63/43.71  tff(c_18, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.63/43.71  tff(c_1785, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1716, c_18])).
% 56.63/43.71  tff(c_34, plain, (![B_25, A_24]: (k2_relat_1(B_25)=A_24 | ~v2_funct_2(B_25, A_24) | ~v5_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.63/43.71  tff(c_1810, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1785, c_34])).
% 56.63/43.71  tff(c_1813, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_1780, c_1810])).
% 56.63/43.71  tff(c_10, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 56.63/43.71  tff(c_1844, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1813, c_10])).
% 56.63/43.71  tff(c_1858, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_82, c_482, c_1844])).
% 56.63/43.71  tff(c_1860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1806, c_1858])).
% 56.63/43.71  tff(c_1861, plain, (k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1652])).
% 56.63/43.71  tff(c_63758, plain, (k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1861])).
% 56.63/43.71  tff(c_1431, plain, (![C_200, F_199, D_196, E_201, A_198, B_197]: (m1_subset_1(k1_partfun1(A_198, B_197, C_200, D_196, E_201, F_199), k1_zfmisc_1(k2_zfmisc_1(A_198, D_196))) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_200, D_196))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))) | ~v1_funct_1(E_201))), inference(cnfTransformation, [status(thm)], [f_119])).
% 56.63/43.71  tff(c_50, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 56.63/43.71  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_502, plain, (![D_128, C_129, A_130, B_131]: (D_128=C_129 | ~r2_relset_1(A_130, B_131, C_129, D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 56.63/43.71  tff(c_510, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_502])).
% 56.63/43.71  tff(c_525, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_510])).
% 56.63/43.71  tff(c_544, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_525])).
% 56.63/43.71  tff(c_1461, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1431, c_544])).
% 56.63/43.71  tff(c_1499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_76, c_74, c_68, c_1461])).
% 56.63/43.71  tff(c_1500, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_525])).
% 56.63/43.71  tff(c_1879, plain, (![F_238, B_242, A_237, C_239, E_240, D_241]: (k1_partfun1(A_237, B_242, C_239, D_241, E_240, F_238)=k5_relat_1(E_240, F_238) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(C_239, D_241))) | ~v1_funct_1(F_238) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_237, B_242))) | ~v1_funct_1(E_240))), inference(cnfTransformation, [status(thm)], [f_149])).
% 56.63/43.71  tff(c_1887, plain, (![A_237, B_242, E_240]: (k1_partfun1(A_237, B_242, '#skF_1', '#skF_1', E_240, '#skF_3')=k5_relat_1(E_240, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_237, B_242))) | ~v1_funct_1(E_240))), inference(resolution, [status(thm)], [c_68, c_1879])).
% 56.63/43.71  tff(c_1986, plain, (![A_243, B_244, E_245]: (k1_partfun1(A_243, B_244, '#skF_1', '#skF_1', E_245, '#skF_3')=k5_relat_1(E_245, '#skF_3') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(E_245))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1887])).
% 56.63/43.71  tff(c_2004, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1986])).
% 56.63/43.71  tff(c_2018, plain, (k5_relat_1('#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1500, c_2004])).
% 56.63/43.71  tff(c_472, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_466])).
% 56.63/43.71  tff(c_479, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_472])).
% 56.63/43.71  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_1519, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1513])).
% 56.63/43.71  tff(c_1526, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1519])).
% 56.63/43.71  tff(c_532, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_526])).
% 56.63/43.71  tff(c_539, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_532])).
% 56.63/43.71  tff(c_1530, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1526, c_539])).
% 56.63/43.71  tff(c_1545, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1541])).
% 56.63/43.71  tff(c_1551, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1526, c_1545])).
% 56.63/43.71  tff(c_1698, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1526, c_1654])).
% 56.63/43.71  tff(c_1718, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_1698])).
% 56.63/43.71  tff(c_1923, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1718, c_26])).
% 56.63/43.71  tff(c_1967, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1530, c_1551, c_1923])).
% 56.63/43.71  tff(c_1937, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1718, c_2])).
% 56.63/43.71  tff(c_1976, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1937])).
% 56.63/43.71  tff(c_1972, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1718, c_18])).
% 56.63/43.71  tff(c_2022, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1972, c_34])).
% 56.63/43.71  tff(c_2025, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_2022])).
% 56.63/43.71  tff(c_63958, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1967, c_2025])).
% 56.63/43.71  tff(c_63968, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_63958, c_10])).
% 56.63/43.71  tff(c_63982, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_74, c_479, c_63968])).
% 56.63/43.71  tff(c_1576, plain, (![B_213]: (k2_funct_1('#skF_3')=B_213 | k5_relat_1(B_213, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_213)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_429, c_1572])).
% 56.63/43.71  tff(c_1580, plain, (![B_213]: (k2_funct_1('#skF_3')=B_213 | k5_relat_1(B_213, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_213)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_213) | ~v1_relat_1(B_213))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_74, c_479, c_1576])).
% 56.63/43.71  tff(c_88650, plain, (![B_1429]: (k2_funct_1('#skF_3')=B_1429 | k5_relat_1(B_1429, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_1429)!='#skF_1' | ~v1_funct_1(B_1429) | ~v1_relat_1(B_1429))), inference(demodulation, [status(thm), theory('equality')], [c_63982, c_1580])).
% 56.63/43.71  tff(c_88938, plain, (k2_funct_1('#skF_3')='#skF_2' | k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_2')!='#skF_1' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_118, c_88650])).
% 56.63/43.71  tff(c_89167, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_359, c_2018, c_88938])).
% 56.63/43.71  tff(c_207, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_50, c_200])).
% 56.63/43.71  tff(c_2395, plain, (![A_261, B_262, C_263, D_264]: (k2_relset_1(A_261, B_262, C_263)=B_262 | ~r2_relset_1(B_262, B_262, k1_partfun1(B_262, A_261, A_261, B_262, D_264, C_263), k6_partfun1(B_262)) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(B_262, A_261))) | ~v1_funct_2(D_264, B_262, A_261) | ~v1_funct_1(D_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2(C_263, A_261, B_262) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_178])).
% 56.63/43.71  tff(c_2404, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1500, c_2395])).
% 56.63/43.71  tff(c_2410, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_82, c_80, c_76, c_207, c_2404])).
% 56.63/43.71  tff(c_6, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 56.63/43.71  tff(c_134, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_118, c_6])).
% 56.63/43.71  tff(c_144, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 56.63/43.71  tff(c_361, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_144])).
% 56.63/43.71  tff(c_2030, plain, (![A_246, C_247, B_248]: (k6_partfun1(A_246)=k5_relat_1(C_247, k2_funct_1(C_247)) | k1_xboole_0=B_248 | ~v2_funct_1(C_247) | k2_relset_1(A_246, B_248, C_247)!=B_248 | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_246, B_248))) | ~v1_funct_2(C_247, A_246, B_248) | ~v1_funct_1(C_247))), inference(cnfTransformation, [status(thm)], [f_194])).
% 56.63/43.71  tff(c_2040, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2030])).
% 56.63/43.71  tff(c_2055, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_479, c_2040])).
% 56.63/43.71  tff(c_2056, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_361, c_2055])).
% 56.63/43.71  tff(c_63753, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2410, c_2056])).
% 56.63/43.71  tff(c_89293, plain, (k5_relat_1('#skF_3', '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_89167, c_63753])).
% 56.63/43.71  tff(c_89395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63758, c_89293])).
% 56.63/43.71  tff(c_89396, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1861])).
% 56.63/43.71  tff(c_64, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 56.63/43.71  tff(c_1536, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_64])).
% 56.63/43.71  tff(c_89415, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89396, c_1536])).
% 56.63/43.71  tff(c_89435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_89415])).
% 56.63/43.71  tff(c_89436, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_134])).
% 56.63/43.71  tff(c_89437, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 56.63/43.71  tff(c_89445, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_89436, c_89437])).
% 56.63/43.71  tff(c_89513, plain, (![C_1435, B_1436, A_1437]: (v5_relat_1(C_1435, B_1436) | ~m1_subset_1(C_1435, k1_zfmisc_1(k2_zfmisc_1(A_1437, B_1436))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.63/43.71  tff(c_89525, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_89513])).
% 56.63/43.71  tff(c_89805, plain, (![B_1487, A_1488]: (k2_relat_1(B_1487)=A_1488 | ~v2_funct_2(B_1487, A_1488) | ~v5_relat_1(B_1487, A_1488) | ~v1_relat_1(B_1487))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.63/43.71  tff(c_89814, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_89525, c_89805])).
% 56.63/43.71  tff(c_89826, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_89445, c_89814])).
% 56.63/43.71  tff(c_89830, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_89826])).
% 56.63/43.71  tff(c_89917, plain, (![C_1504, B_1505, A_1506]: (v2_funct_2(C_1504, B_1505) | ~v3_funct_2(C_1504, A_1506, B_1505) | ~v1_funct_1(C_1504) | ~m1_subset_1(C_1504, k1_zfmisc_1(k2_zfmisc_1(A_1506, B_1505))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_89926, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_76, c_89917])).
% 56.63/43.71  tff(c_89933, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_89926])).
% 56.63/43.71  tff(c_89935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89830, c_89933])).
% 56.63/43.71  tff(c_89936, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_89826])).
% 56.63/43.71  tff(c_126, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_117, c_6])).
% 56.63/43.71  tff(c_89452, plain, (k2_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_89436, c_89436, c_126])).
% 56.63/43.71  tff(c_89453, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_89452])).
% 56.63/43.71  tff(c_89949, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_89936, c_89453])).
% 56.63/43.71  tff(c_89524, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_89513])).
% 56.63/43.71  tff(c_89817, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89524, c_89805])).
% 56.63/43.71  tff(c_89829, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_89817])).
% 56.63/43.71  tff(c_90006, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_89949, c_89829])).
% 56.63/43.71  tff(c_90040, plain, (![C_1511, B_1512, A_1513]: (v2_funct_2(C_1511, B_1512) | ~v3_funct_2(C_1511, A_1513, B_1512) | ~v1_funct_1(C_1511) | ~m1_subset_1(C_1511, k1_zfmisc_1(k2_zfmisc_1(A_1513, B_1512))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_90049, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_90040])).
% 56.63/43.71  tff(c_90056, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_90049])).
% 56.63/43.71  tff(c_90058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90006, c_90056])).
% 56.63/43.71  tff(c_90059, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_89452])).
% 56.63/43.71  tff(c_90060, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_89452])).
% 56.63/43.71  tff(c_90084, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90059, c_90060])).
% 56.63/43.71  tff(c_90148, plain, (![C_1524, B_1525, A_1526]: (v5_relat_1(C_1524, B_1525) | ~m1_subset_1(C_1524, k1_zfmisc_1(k2_zfmisc_1(A_1526, B_1525))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.63/43.71  tff(c_90156, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_90148])).
% 56.63/43.71  tff(c_90333, plain, (![B_1559, A_1560]: (k2_relat_1(B_1559)=A_1560 | ~v2_funct_2(B_1559, A_1560) | ~v5_relat_1(B_1559, A_1560) | ~v1_relat_1(B_1559))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.63/43.71  tff(c_90342, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90156, c_90333])).
% 56.63/43.71  tff(c_90351, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90084, c_90342])).
% 56.63/43.71  tff(c_90352, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_90351])).
% 56.63/43.71  tff(c_90374, plain, (![C_1570, B_1571, A_1572]: (v2_funct_2(C_1570, B_1571) | ~v3_funct_2(C_1570, A_1572, B_1571) | ~v1_funct_1(C_1570) | ~m1_subset_1(C_1570, k1_zfmisc_1(k2_zfmisc_1(A_1572, B_1571))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_90380, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_90374])).
% 56.63/43.71  tff(c_90384, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_90380])).
% 56.63/43.71  tff(c_90386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90352, c_90384])).
% 56.63/43.71  tff(c_90387, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_90351])).
% 56.63/43.71  tff(c_8, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 56.63/43.71  tff(c_125, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_117, c_8])).
% 56.63/43.71  tff(c_89450, plain, (k1_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_89436, c_89436, c_125])).
% 56.63/43.71  tff(c_89451, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_89450])).
% 56.63/43.71  tff(c_90061, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90059, c_89451])).
% 56.63/43.71  tff(c_90400, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90387, c_90387, c_90061])).
% 56.63/43.71  tff(c_90405, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90387, c_117])).
% 56.63/43.71  tff(c_90409, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90387, c_74])).
% 56.63/43.71  tff(c_90408, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90387, c_70])).
% 56.63/43.71  tff(c_90406, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_90387, c_68])).
% 56.63/43.71  tff(c_28, plain, (![C_23, A_21, B_22]: (v2_funct_1(C_23) | ~v3_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_90451, plain, (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_90406, c_28])).
% 56.63/43.71  tff(c_90468, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90409, c_90408, c_90451])).
% 56.63/43.71  tff(c_90407, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90387, c_72])).
% 56.63/43.71  tff(c_90564, plain, (![A_1602, B_1603]: (k2_funct_2(A_1602, B_1603)=k2_funct_1(B_1603) | ~m1_subset_1(B_1603, k1_zfmisc_1(k2_zfmisc_1(A_1602, A_1602))) | ~v3_funct_2(B_1603, A_1602, A_1602) | ~v1_funct_2(B_1603, A_1602, A_1602) | ~v1_funct_1(B_1603))), inference(cnfTransformation, [status(thm)], [f_159])).
% 56.63/43.71  tff(c_90567, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_90406, c_90564])).
% 56.63/43.71  tff(c_90573, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90409, c_90407, c_90408, c_90567])).
% 56.63/43.71  tff(c_90609, plain, (![A_1613, B_1614]: (m1_subset_1(k2_funct_2(A_1613, B_1614), k1_zfmisc_1(k2_zfmisc_1(A_1613, A_1613))) | ~m1_subset_1(B_1614, k1_zfmisc_1(k2_zfmisc_1(A_1613, A_1613))) | ~v3_funct_2(B_1614, A_1613, A_1613) | ~v1_funct_2(B_1614, A_1613, A_1613) | ~v1_funct_1(B_1614))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_90642, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90573, c_90609])).
% 56.63/43.71  tff(c_90657, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_90409, c_90407, c_90408, c_90406, c_90642])).
% 56.63/43.71  tff(c_90684, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_90657, c_2])).
% 56.63/43.71  tff(c_90711, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90684])).
% 56.63/43.71  tff(c_90547, plain, (![A_1598, B_1599]: (v1_funct_1(k2_funct_2(A_1598, B_1599)) | ~m1_subset_1(B_1599, k1_zfmisc_1(k2_zfmisc_1(A_1598, A_1598))) | ~v3_funct_2(B_1599, A_1598, A_1598) | ~v1_funct_2(B_1599, A_1598, A_1598) | ~v1_funct_1(B_1599))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_90550, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_90406, c_90547])).
% 56.63/43.71  tff(c_90556, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90409, c_90407, c_90408, c_90550])).
% 56.63/43.71  tff(c_90575, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90573, c_90556])).
% 56.63/43.71  tff(c_90581, plain, (![A_1604, B_1605]: (v3_funct_2(k2_funct_2(A_1604, B_1605), A_1604, A_1604) | ~m1_subset_1(B_1605, k1_zfmisc_1(k2_zfmisc_1(A_1604, A_1604))) | ~v3_funct_2(B_1605, A_1604, A_1604) | ~v1_funct_2(B_1605, A_1604, A_1604) | ~v1_funct_1(B_1605))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_90583, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_90406, c_90581])).
% 56.63/43.71  tff(c_90588, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90409, c_90407, c_90408, c_90573, c_90583])).
% 56.63/43.71  tff(c_90670, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_90657, c_26])).
% 56.63/43.71  tff(c_90702, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90575, c_90588, c_90670])).
% 56.63/43.71  tff(c_90707, plain, (v5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_90657, c_18])).
% 56.63/43.71  tff(c_90724, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_90707, c_34])).
% 56.63/43.71  tff(c_90727, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90711, c_90702, c_90724])).
% 56.63/43.71  tff(c_90736, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90727, c_10])).
% 56.63/43.71  tff(c_90750, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90405, c_90409, c_90468, c_90736])).
% 56.63/43.71  tff(c_90752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90400, c_90750])).
% 56.63/43.71  tff(c_90753, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_89450])).
% 56.63/43.71  tff(c_90755, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90753, c_90753, c_89445])).
% 56.63/43.71  tff(c_90839, plain, (![C_1621, B_1622, A_1623]: (v5_relat_1(C_1621, B_1622) | ~m1_subset_1(C_1621, k1_zfmisc_1(k2_zfmisc_1(A_1623, B_1622))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 56.63/43.71  tff(c_90847, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_90839])).
% 56.63/43.71  tff(c_91009, plain, (![B_1651, A_1652]: (k2_relat_1(B_1651)=A_1652 | ~v2_funct_2(B_1651, A_1652) | ~v5_relat_1(B_1651, A_1652) | ~v1_relat_1(B_1651))), inference(cnfTransformation, [status(thm)], [f_107])).
% 56.63/43.71  tff(c_91015, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90847, c_91009])).
% 56.63/43.71  tff(c_91021, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_90755, c_91015])).
% 56.63/43.71  tff(c_91028, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_91021])).
% 56.63/43.71  tff(c_91070, plain, (![C_1663, B_1664, A_1665]: (v2_funct_2(C_1663, B_1664) | ~v3_funct_2(C_1663, A_1665, B_1664) | ~v1_funct_1(C_1663) | ~m1_subset_1(C_1663, k1_zfmisc_1(k2_zfmisc_1(A_1665, B_1664))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 56.63/43.71  tff(c_91076, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_91070])).
% 56.63/43.71  tff(c_91080, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_91076])).
% 56.63/43.71  tff(c_91082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91028, c_91080])).
% 56.63/43.71  tff(c_91083, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_91021])).
% 56.63/43.71  tff(c_91101, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91083, c_68])).
% 56.63/43.71  tff(c_91218, plain, (![A_1672, B_1673, D_1674]: (r2_relset_1(A_1672, B_1673, D_1674, D_1674) | ~m1_subset_1(D_1674, k1_zfmisc_1(k2_zfmisc_1(A_1672, B_1673))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 56.63/43.71  tff(c_91223, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_91101, c_91218])).
% 56.63/43.71  tff(c_91104, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91083, c_74])).
% 56.63/43.71  tff(c_91102, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91083, c_72])).
% 56.63/43.71  tff(c_91103, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91083, c_70])).
% 56.63/43.71  tff(c_91288, plain, (![A_1697, B_1698]: (k2_funct_2(A_1697, B_1698)=k2_funct_1(B_1698) | ~m1_subset_1(B_1698, k1_zfmisc_1(k2_zfmisc_1(A_1697, A_1697))) | ~v3_funct_2(B_1698, A_1697, A_1697) | ~v1_funct_2(B_1698, A_1697, A_1697) | ~v1_funct_1(B_1698))), inference(cnfTransformation, [status(thm)], [f_159])).
% 56.63/43.71  tff(c_91291, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_91101, c_91288])).
% 56.63/43.71  tff(c_91297, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91104, c_91102, c_91103, c_91291])).
% 56.63/43.71  tff(c_91371, plain, (![A_1721, B_1722]: (m1_subset_1(k2_funct_2(A_1721, B_1722), k1_zfmisc_1(k2_zfmisc_1(A_1721, A_1721))) | ~m1_subset_1(B_1722, k1_zfmisc_1(k2_zfmisc_1(A_1721, A_1721))) | ~v3_funct_2(B_1722, A_1721, A_1721) | ~v1_funct_2(B_1722, A_1721, A_1721) | ~v1_funct_1(B_1722))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_91409, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_91297, c_91371])).
% 56.63/43.71  tff(c_91426, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91104, c_91102, c_91103, c_91101, c_91409])).
% 56.63/43.71  tff(c_91458, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_91426, c_2])).
% 56.63/43.71  tff(c_91491, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_91458])).
% 56.63/43.71  tff(c_91272, plain, (![A_1693, B_1694]: (v1_funct_1(k2_funct_2(A_1693, B_1694)) | ~m1_subset_1(B_1694, k1_zfmisc_1(k2_zfmisc_1(A_1693, A_1693))) | ~v3_funct_2(B_1694, A_1693, A_1693) | ~v1_funct_2(B_1694, A_1693, A_1693) | ~v1_funct_1(B_1694))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_91275, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_91101, c_91272])).
% 56.63/43.71  tff(c_91281, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91104, c_91102, c_91103, c_91275])).
% 56.63/43.71  tff(c_91299, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91297, c_91281])).
% 56.63/43.71  tff(c_91316, plain, (![A_1703, B_1704]: (v3_funct_2(k2_funct_2(A_1703, B_1704), A_1703, A_1703) | ~m1_subset_1(B_1704, k1_zfmisc_1(k2_zfmisc_1(A_1703, A_1703))) | ~v3_funct_2(B_1704, A_1703, A_1703) | ~v1_funct_2(B_1704, A_1703, A_1703) | ~v1_funct_1(B_1704))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.63/43.71  tff(c_91318, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_91101, c_91316])).
% 56.63/43.71  tff(c_91323, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91104, c_91102, c_91103, c_91297, c_91318])).
% 56.63/43.71  tff(c_91444, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_91426, c_26])).
% 56.63/43.71  tff(c_91482, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91299, c_91323, c_91444])).
% 56.63/43.71  tff(c_91488, plain, (v5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_91426, c_18])).
% 56.63/43.71  tff(c_91512, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_91488, c_34])).
% 56.63/43.71  tff(c_91515, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91491, c_91482, c_91512])).
% 56.63/43.71  tff(c_89439, plain, (![A_6]: (k2_relat_1(A_6)!='#skF_2' | A_6='#skF_2' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_89436, c_89436, c_6])).
% 56.63/43.71  tff(c_90803, plain, (![A_6]: (k2_relat_1(A_6)!='#skF_3' | A_6='#skF_3' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_90753, c_90753, c_89439])).
% 56.63/43.71  tff(c_91093, plain, (![A_6]: (k2_relat_1(A_6)!='#skF_1' | A_6='#skF_1' | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_91083, c_91083, c_90803])).
% 56.63/43.71  tff(c_91507, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_91491, c_91093])).
% 56.63/43.71  tff(c_91601, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91515, c_91507])).
% 56.63/43.71  tff(c_90759, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90753, c_64])).
% 56.63/43.71  tff(c_91095, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91083, c_91083, c_90759])).
% 56.63/43.71  tff(c_91300, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91297, c_91095])).
% 56.63/43.71  tff(c_91619, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91601, c_91300])).
% 56.63/43.71  tff(c_91637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91223, c_91619])).
% 56.63/43.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.63/43.71  
% 56.63/43.71  Inference rules
% 56.63/43.71  ----------------------
% 56.63/43.71  #Ref     : 0
% 56.63/43.71  #Sup     : 18229
% 56.63/43.71  #Fact    : 0
% 56.63/43.71  #Define  : 0
% 56.63/43.71  #Split   : 283
% 56.63/43.71  #Chain   : 0
% 56.63/43.71  #Close   : 0
% 56.63/43.71  
% 56.63/43.71  Ordering : KBO
% 56.63/43.71  
% 56.63/43.71  Simplification rules
% 56.63/43.71  ----------------------
% 56.63/43.71  #Subsume      : 1070
% 56.63/43.71  #Demod        : 55973
% 56.63/43.71  #Tautology    : 2226
% 56.63/43.71  #SimpNegUnit  : 1412
% 56.63/43.71  #BackRed      : 1851
% 56.63/43.71  
% 56.63/43.71  #Partial instantiations: 0
% 56.63/43.71  #Strategies tried      : 1
% 56.63/43.71  
% 56.63/43.71  Timing (in seconds)
% 56.63/43.71  ----------------------
% 56.63/43.71  Preprocessing        : 0.49
% 56.63/43.71  Parsing              : 0.29
% 56.63/43.71  CNF conversion       : 0.03
% 56.63/43.71  Main loop            : 42.35
% 56.63/43.71  Inferencing          : 5.36
% 56.63/43.71  Reduction            : 27.34
% 56.63/43.71  Demodulation         : 24.62
% 56.63/43.71  BG Simplification    : 0.35
% 56.63/43.71  Subsumption          : 7.82
% 56.63/43.71  Abstraction          : 0.65
% 56.63/43.71  MUC search           : 0.00
% 56.63/43.71  Cooper               : 0.00
% 56.63/43.71  Total                : 42.93
% 56.63/43.71  Index Insertion      : 0.00
% 56.63/43.71  Index Deletion       : 0.00
% 56.63/43.71  Index Matching       : 0.00
% 56.63/43.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
