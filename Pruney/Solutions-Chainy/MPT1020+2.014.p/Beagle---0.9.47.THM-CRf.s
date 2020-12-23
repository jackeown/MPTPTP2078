%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 10.25s
% Output     : CNFRefutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 716 expanded)
%              Number of leaves         :   57 ( 265 expanded)
%              Depth                    :   11
%              Number of atoms          :  310 (1941 expanded)
%              Number of equality atoms :   81 ( 287 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
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

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_176,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_172,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_232,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_186,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_188,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_2021,plain,(
    ! [A_251,B_252,D_253] :
      ( r2_relset_1(A_251,B_252,D_253,D_253)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2037,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_2021])).

tff(c_648,plain,(
    ! [C_148,A_149,B_150] :
      ( v1_xboole_0(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_670,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_648])).

tff(c_674,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_670])).

tff(c_110,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_108,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_102,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_100,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_282,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_304,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_282])).

tff(c_432,plain,(
    ! [C_115,B_116,A_117] :
      ( v5_relat_1(C_115,B_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_455,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_432])).

tff(c_697,plain,(
    ! [B_154,A_155] :
      ( k2_relat_1(B_154) = A_155
      | ~ v2_funct_2(B_154,A_155)
      | ~ v5_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_712,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_697])).

tff(c_728,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_712])).

tff(c_759,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_106,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_1517,plain,(
    ! [C_219,B_220,A_221] :
      ( v2_funct_2(C_219,B_220)
      | ~ v3_funct_2(C_219,A_221,B_220)
      | ~ v1_funct_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1533,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1517])).

tff(c_1546,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_1533])).

tff(c_1548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_759,c_1546])).

tff(c_1549,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_2127,plain,(
    ! [A_260,B_261,C_262] :
      ( k2_relset_1(A_260,B_261,C_262) = k2_relat_1(C_262)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2143,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_2127])).

tff(c_2153,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_2143])).

tff(c_80,plain,(
    ! [A_58] : m1_subset_1(k6_partfun1(A_58),k1_zfmisc_1(k2_zfmisc_1(A_58,A_58))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2036,plain,(
    ! [A_58] : r2_relset_1(A_58,A_58,k6_partfun1(A_58),k6_partfun1(A_58)) ),
    inference(resolution,[status(thm)],[c_80,c_2021])).

tff(c_2177,plain,(
    ! [C_264,A_265,B_266] :
      ( v2_funct_1(C_264)
      | ~ v3_funct_2(C_264,A_265,B_266)
      | ~ v1_funct_1(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2193,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_2177])).

tff(c_2206,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_2193])).

tff(c_74,plain,(
    ! [D_55,F_57,B_53,A_52,E_56,C_54] :
      ( m1_subset_1(k1_partfun1(A_52,B_53,C_54,D_55,E_56,F_57),k1_zfmisc_1(k2_zfmisc_1(A_52,D_55)))
      | ~ m1_subset_1(F_57,k1_zfmisc_1(k2_zfmisc_1(C_54,D_55)))
      | ~ v1_funct_1(F_57)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(E_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_94,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_2304,plain,(
    ! [D_279,C_280,A_281,B_282] :
      ( D_279 = C_280
      | ~ r2_relset_1(A_281,B_282,C_280,D_279)
      | ~ m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2314,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_94,c_2304])).

tff(c_2333,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2314])).

tff(c_2752,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2333])).

tff(c_4003,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2752])).

tff(c_4010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_104,c_102,c_96,c_4003])).

tff(c_4011,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_4') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2333])).

tff(c_5994,plain,(
    ! [C_436,D_437,B_438,A_439] :
      ( k2_funct_1(C_436) = D_437
      | k1_xboole_0 = B_438
      | k1_xboole_0 = A_439
      | ~ v2_funct_1(C_436)
      | ~ r2_relset_1(A_439,A_439,k1_partfun1(A_439,B_438,B_438,A_439,C_436,D_437),k6_partfun1(A_439))
      | k2_relset_1(A_439,B_438,C_436) != B_438
      | ~ m1_subset_1(D_437,k1_zfmisc_1(k2_zfmisc_1(B_438,A_439)))
      | ~ v1_funct_2(D_437,B_438,A_439)
      | ~ v1_funct_1(D_437)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_439,B_438)))
      | ~ v1_funct_2(C_436,A_439,B_438)
      | ~ v1_funct_1(C_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_6000,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4011,c_5994])).

tff(c_6017,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_104,c_102,c_100,c_96,c_2153,c_2036,c_2206,c_6000])).

tff(c_6020,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6017])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6087,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6020,c_8])).

tff(c_6089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_6087])).

tff(c_6090,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6017])).

tff(c_2387,plain,(
    ! [A_292,B_293] :
      ( k2_funct_2(A_292,B_293) = k2_funct_1(B_293)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(k2_zfmisc_1(A_292,A_292)))
      | ~ v3_funct_2(B_293,A_292,A_292)
      | ~ v1_funct_2(B_293,A_292,A_292)
      | ~ v1_funct_1(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2404,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_2387])).

tff(c_2418,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_106,c_2404])).

tff(c_92,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_2423,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_92])).

tff(c_6107,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6090,c_2423])).

tff(c_6111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_6107])).

tff(c_6112,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_670])).

tff(c_211,plain,(
    ! [B_83,A_84] :
      ( ~ v1_xboole_0(B_83)
      | B_83 = A_84
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,(
    ! [A_84] :
      ( k1_xboole_0 = A_84
      | ~ v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_8,c_211])).

tff(c_6119,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6112,c_214])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6152,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_10])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6184,plain,(
    ! [A_442,B_443,D_444] :
      ( r2_relset_1(A_442,B_443,D_444,D_444)
      | ~ m1_subset_1(D_444,k1_zfmisc_1(k2_zfmisc_1(A_442,B_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_9491,plain,(
    ! [A_600,B_601,A_602] :
      ( r2_relset_1(A_600,B_601,A_602,A_602)
      | ~ r1_tarski(A_602,k2_zfmisc_1(A_600,B_601)) ) ),
    inference(resolution,[status(thm)],[c_24,c_6184])).

tff(c_9512,plain,(
    ! [A_600,B_601] : r2_relset_1(A_600,B_601,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6152,c_9491])).

tff(c_6113,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_670])).

tff(c_6126,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6113,c_214])).

tff(c_6161,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_6126])).

tff(c_6178,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6161,c_6161,c_100])).

tff(c_153,plain,(
    ! [A_81] : k6_relat_1(A_81) = k6_partfun1(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_34])).

tff(c_6149,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6119,c_6119,c_159])).

tff(c_98,plain,(
    v3_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_6176,plain,(
    v3_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6161,c_6161,c_98])).

tff(c_84,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_113,plain,(
    ! [A_24] : v1_relat_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_42])).

tff(c_40,plain,(
    ! [A_23] : v1_funct_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    ! [A_23] : v1_funct_1(k6_partfun1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_40])).

tff(c_44,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_112,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_44])).

tff(c_30,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_30])).

tff(c_28,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_118,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_28])).

tff(c_32,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_305,plain,(
    ! [A_99] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_99)),A_99) = A_99
      | ~ v1_relat_1(A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_32])).

tff(c_317,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19)
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_305])).

tff(c_323,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_317])).

tff(c_46,plain,(
    ! [A_25,B_27] :
      ( k2_funct_1(A_25) = B_27
      | k6_relat_1(k2_relat_1(A_25)) != k5_relat_1(B_27,A_25)
      | k2_relat_1(B_27) != k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6802,plain,(
    ! [A_486,B_487] :
      ( k2_funct_1(A_486) = B_487
      | k6_partfun1(k2_relat_1(A_486)) != k5_relat_1(B_487,A_486)
      | k2_relat_1(B_487) != k1_relat_1(A_486)
      | ~ v2_funct_1(A_486)
      | ~ v1_funct_1(B_487)
      | ~ v1_relat_1(B_487)
      | ~ v1_funct_1(A_486)
      | ~ v1_relat_1(A_486) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46])).

tff(c_6806,plain,(
    ! [A_19] :
      ( k2_funct_1(k6_partfun1(A_19)) = k6_partfun1(A_19)
      | k6_partfun1(k2_relat_1(k6_partfun1(A_19))) != k6_partfun1(A_19)
      | k2_relat_1(k6_partfun1(A_19)) != k1_relat_1(k6_partfun1(A_19))
      | ~ v2_funct_1(k6_partfun1(A_19))
      | ~ v1_funct_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19))
      | ~ v1_funct_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_6802])).

tff(c_6814,plain,(
    ! [A_19] : k2_funct_1(k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_114,c_113,c_114,c_112,c_117,c_118,c_117,c_6806])).

tff(c_6694,plain,(
    ! [A_482,B_483] :
      ( k2_funct_2(A_482,B_483) = k2_funct_1(B_483)
      | ~ m1_subset_1(B_483,k1_zfmisc_1(k2_zfmisc_1(A_482,A_482)))
      | ~ v3_funct_2(B_483,A_482,A_482)
      | ~ v1_funct_2(B_483,A_482,A_482)
      | ~ v1_funct_1(B_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_6709,plain,(
    ! [A_58] :
      ( k2_funct_2(A_58,k6_partfun1(A_58)) = k2_funct_1(k6_partfun1(A_58))
      | ~ v3_funct_2(k6_partfun1(A_58),A_58,A_58)
      | ~ v1_funct_2(k6_partfun1(A_58),A_58,A_58)
      | ~ v1_funct_1(k6_partfun1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_80,c_6694])).

tff(c_6713,plain,(
    ! [A_58] :
      ( k2_funct_2(A_58,k6_partfun1(A_58)) = k2_funct_1(k6_partfun1(A_58))
      | ~ v3_funct_2(k6_partfun1(A_58),A_58,A_58)
      | ~ v1_funct_2(k6_partfun1(A_58),A_58,A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_6709])).

tff(c_16082,plain,(
    ! [A_756] :
      ( k2_funct_2(A_756,k6_partfun1(A_756)) = k6_partfun1(A_756)
      | ~ v3_funct_2(k6_partfun1(A_756),A_756,A_756)
      | ~ v1_funct_2(k6_partfun1(A_756),A_756,A_756) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_6713])).

tff(c_16115,plain,
    ( k2_funct_2('#skF_4',k6_partfun1('#skF_4')) = k6_partfun1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2(k6_partfun1('#skF_4'),'#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6149,c_16082])).

tff(c_16117,plain,(
    k2_funct_2('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6178,c_6149,c_6176,c_6149,c_6149,c_16115])).

tff(c_673,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_648])).

tff(c_6208,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6112,c_6161,c_673])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(B_8)
      | B_8 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6127,plain,(
    ! [A_7] :
      ( A_7 = '#skF_2'
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_6113,c_12])).

tff(c_6367,plain,(
    ! [A_452] :
      ( A_452 = '#skF_4'
      | ~ v1_xboole_0(A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6161,c_6127])).

tff(c_6374,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6208,c_6367])).

tff(c_6172,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6161,c_6161,c_6161,c_92])).

tff(c_6607,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6374,c_6172])).

tff(c_16118,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16117,c_6607])).

tff(c_16121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9512,c_16118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.25/3.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.46  
% 10.25/3.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.46  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.25/3.46  
% 10.25/3.46  %Foreground sorts:
% 10.25/3.46  
% 10.25/3.46  
% 10.25/3.46  %Background operators:
% 10.25/3.46  
% 10.25/3.46  
% 10.25/3.46  %Foreground operators:
% 10.25/3.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.25/3.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.25/3.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.25/3.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.25/3.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.25/3.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.25/3.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.25/3.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.25/3.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.25/3.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.25/3.46  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 10.25/3.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.25/3.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.25/3.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.25/3.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.25/3.46  tff('#skF_2', type, '#skF_2': $i).
% 10.25/3.46  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.25/3.46  tff('#skF_3', type, '#skF_3': $i).
% 10.25/3.46  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.25/3.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.25/3.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.25/3.46  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.25/3.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.25/3.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.25/3.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.25/3.46  tff('#skF_4', type, '#skF_4': $i).
% 10.25/3.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.25/3.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.25/3.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.25/3.46  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 10.25/3.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.25/3.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.25/3.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.25/3.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.25/3.46  
% 10.34/3.49  tff(f_254, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 10.34/3.49  tff(f_140, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.34/3.49  tff(f_128, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 10.34/3.49  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.34/3.49  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.34/3.49  tff(f_160, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 10.34/3.49  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.34/3.49  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.34/3.49  tff(f_176, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.34/3.49  tff(f_172, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.34/3.49  tff(f_232, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.34/3.49  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.34/3.49  tff(f_186, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.34/3.49  tff(f_43, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 10.34/3.49  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.34/3.49  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.34/3.49  tff(f_188, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.34/3.49  tff(f_75, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 10.34/3.49  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.34/3.49  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.34/3.49  tff(f_70, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.34/3.49  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 10.34/3.49  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 10.34/3.49  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_2021, plain, (![A_251, B_252, D_253]: (r2_relset_1(A_251, B_252, D_253, D_253) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.34/3.49  tff(c_2037, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_2021])).
% 10.34/3.49  tff(c_648, plain, (![C_148, A_149, B_150]: (v1_xboole_0(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.34/3.49  tff(c_670, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_96, c_648])).
% 10.34/3.49  tff(c_674, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_670])).
% 10.34/3.49  tff(c_110, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_108, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_102, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_100, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_282, plain, (![C_96, A_97, B_98]: (v1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.34/3.49  tff(c_304, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_282])).
% 10.34/3.49  tff(c_432, plain, (![C_115, B_116, A_117]: (v5_relat_1(C_115, B_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.34/3.49  tff(c_455, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_104, c_432])).
% 10.34/3.49  tff(c_697, plain, (![B_154, A_155]: (k2_relat_1(B_154)=A_155 | ~v2_funct_2(B_154, A_155) | ~v5_relat_1(B_154, A_155) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.34/3.49  tff(c_712, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_455, c_697])).
% 10.34/3.49  tff(c_728, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_304, c_712])).
% 10.34/3.49  tff(c_759, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_728])).
% 10.34/3.49  tff(c_106, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_1517, plain, (![C_219, B_220, A_221]: (v2_funct_2(C_219, B_220) | ~v3_funct_2(C_219, A_221, B_220) | ~v1_funct_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.34/3.49  tff(c_1533, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1517])).
% 10.34/3.49  tff(c_1546, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_1533])).
% 10.34/3.49  tff(c_1548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_759, c_1546])).
% 10.34/3.49  tff(c_1549, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_728])).
% 10.34/3.49  tff(c_2127, plain, (![A_260, B_261, C_262]: (k2_relset_1(A_260, B_261, C_262)=k2_relat_1(C_262) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.34/3.49  tff(c_2143, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_2127])).
% 10.34/3.49  tff(c_2153, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_2143])).
% 10.34/3.49  tff(c_80, plain, (![A_58]: (m1_subset_1(k6_partfun1(A_58), k1_zfmisc_1(k2_zfmisc_1(A_58, A_58))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.34/3.49  tff(c_2036, plain, (![A_58]: (r2_relset_1(A_58, A_58, k6_partfun1(A_58), k6_partfun1(A_58)))), inference(resolution, [status(thm)], [c_80, c_2021])).
% 10.34/3.49  tff(c_2177, plain, (![C_264, A_265, B_266]: (v2_funct_1(C_264) | ~v3_funct_2(C_264, A_265, B_266) | ~v1_funct_1(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.34/3.49  tff(c_2193, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_2177])).
% 10.34/3.49  tff(c_2206, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_2193])).
% 10.34/3.49  tff(c_74, plain, (![D_55, F_57, B_53, A_52, E_56, C_54]: (m1_subset_1(k1_partfun1(A_52, B_53, C_54, D_55, E_56, F_57), k1_zfmisc_1(k2_zfmisc_1(A_52, D_55))) | ~m1_subset_1(F_57, k1_zfmisc_1(k2_zfmisc_1(C_54, D_55))) | ~v1_funct_1(F_57) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(E_56))), inference(cnfTransformation, [status(thm)], [f_172])).
% 10.34/3.49  tff(c_94, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_2304, plain, (![D_279, C_280, A_281, B_282]: (D_279=C_280 | ~r2_relset_1(A_281, B_282, C_280, D_279) | ~m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.34/3.49  tff(c_2314, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_94, c_2304])).
% 10.34/3.49  tff(c_2333, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2314])).
% 10.34/3.49  tff(c_2752, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2333])).
% 10.34/3.49  tff(c_4003, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2752])).
% 10.34/3.49  tff(c_4010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_104, c_102, c_96, c_4003])).
% 10.34/3.49  tff(c_4011, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_4')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2333])).
% 10.34/3.49  tff(c_5994, plain, (![C_436, D_437, B_438, A_439]: (k2_funct_1(C_436)=D_437 | k1_xboole_0=B_438 | k1_xboole_0=A_439 | ~v2_funct_1(C_436) | ~r2_relset_1(A_439, A_439, k1_partfun1(A_439, B_438, B_438, A_439, C_436, D_437), k6_partfun1(A_439)) | k2_relset_1(A_439, B_438, C_436)!=B_438 | ~m1_subset_1(D_437, k1_zfmisc_1(k2_zfmisc_1(B_438, A_439))) | ~v1_funct_2(D_437, B_438, A_439) | ~v1_funct_1(D_437) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_439, B_438))) | ~v1_funct_2(C_436, A_439, B_438) | ~v1_funct_1(C_436))), inference(cnfTransformation, [status(thm)], [f_232])).
% 10.34/3.49  tff(c_6000, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4011, c_5994])).
% 10.34/3.49  tff(c_6017, plain, (k2_funct_1('#skF_3')='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_104, c_102, c_100, c_96, c_2153, c_2036, c_2206, c_6000])).
% 10.34/3.49  tff(c_6020, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6017])).
% 10.34/3.49  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.34/3.49  tff(c_6087, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6020, c_8])).
% 10.34/3.49  tff(c_6089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_674, c_6087])).
% 10.34/3.49  tff(c_6090, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_6017])).
% 10.34/3.49  tff(c_2387, plain, (![A_292, B_293]: (k2_funct_2(A_292, B_293)=k2_funct_1(B_293) | ~m1_subset_1(B_293, k1_zfmisc_1(k2_zfmisc_1(A_292, A_292))) | ~v3_funct_2(B_293, A_292, A_292) | ~v1_funct_2(B_293, A_292, A_292) | ~v1_funct_1(B_293))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.34/3.49  tff(c_2404, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_2387])).
% 10.34/3.49  tff(c_2418, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_106, c_2404])).
% 10.34/3.49  tff(c_92, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_2423, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_92])).
% 10.34/3.49  tff(c_6107, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6090, c_2423])).
% 10.34/3.49  tff(c_6111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2037, c_6107])).
% 10.34/3.49  tff(c_6112, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_670])).
% 10.34/3.49  tff(c_211, plain, (![B_83, A_84]: (~v1_xboole_0(B_83) | B_83=A_84 | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.34/3.49  tff(c_214, plain, (![A_84]: (k1_xboole_0=A_84 | ~v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_8, c_211])).
% 10.34/3.49  tff(c_6119, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6112, c_214])).
% 10.34/3.49  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.34/3.49  tff(c_6152, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_10])).
% 10.34/3.49  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.34/3.49  tff(c_6184, plain, (![A_442, B_443, D_444]: (r2_relset_1(A_442, B_443, D_444, D_444) | ~m1_subset_1(D_444, k1_zfmisc_1(k2_zfmisc_1(A_442, B_443))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.34/3.49  tff(c_9491, plain, (![A_600, B_601, A_602]: (r2_relset_1(A_600, B_601, A_602, A_602) | ~r1_tarski(A_602, k2_zfmisc_1(A_600, B_601)))), inference(resolution, [status(thm)], [c_24, c_6184])).
% 10.34/3.49  tff(c_9512, plain, (![A_600, B_601]: (r2_relset_1(A_600, B_601, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_6152, c_9491])).
% 10.34/3.49  tff(c_6113, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_670])).
% 10.34/3.49  tff(c_6126, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_6113, c_214])).
% 10.34/3.49  tff(c_6161, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_6126])).
% 10.34/3.49  tff(c_6178, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6161, c_6161, c_100])).
% 10.34/3.49  tff(c_153, plain, (![A_81]: (k6_relat_1(A_81)=k6_partfun1(A_81))), inference(cnfTransformation, [status(thm)], [f_188])).
% 10.34/3.49  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.34/3.49  tff(c_159, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_153, c_34])).
% 10.34/3.49  tff(c_6149, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6119, c_6119, c_159])).
% 10.34/3.49  tff(c_98, plain, (v3_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 10.34/3.49  tff(c_6176, plain, (v3_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6161, c_6161, c_98])).
% 10.34/3.49  tff(c_84, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_188])).
% 10.34/3.49  tff(c_42, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.49  tff(c_113, plain, (![A_24]: (v1_relat_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_42])).
% 10.34/3.49  tff(c_40, plain, (![A_23]: (v1_funct_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.34/3.49  tff(c_114, plain, (![A_23]: (v1_funct_1(k6_partfun1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_40])).
% 10.34/3.49  tff(c_44, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.34/3.49  tff(c_112, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_44])).
% 10.34/3.49  tff(c_30, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.34/3.49  tff(c_117, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_30])).
% 10.34/3.49  tff(c_28, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.34/3.49  tff(c_118, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_28])).
% 10.34/3.49  tff(c_32, plain, (![A_20]: (k5_relat_1(k6_relat_1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.34/3.49  tff(c_305, plain, (![A_99]: (k5_relat_1(k6_partfun1(k1_relat_1(A_99)), A_99)=A_99 | ~v1_relat_1(A_99))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_32])).
% 10.34/3.49  tff(c_317, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_305])).
% 10.34/3.49  tff(c_323, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_317])).
% 10.34/3.49  tff(c_46, plain, (![A_25, B_27]: (k2_funct_1(A_25)=B_27 | k6_relat_1(k2_relat_1(A_25))!=k5_relat_1(B_27, A_25) | k2_relat_1(B_27)!=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.34/3.49  tff(c_6802, plain, (![A_486, B_487]: (k2_funct_1(A_486)=B_487 | k6_partfun1(k2_relat_1(A_486))!=k5_relat_1(B_487, A_486) | k2_relat_1(B_487)!=k1_relat_1(A_486) | ~v2_funct_1(A_486) | ~v1_funct_1(B_487) | ~v1_relat_1(B_487) | ~v1_funct_1(A_486) | ~v1_relat_1(A_486))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46])).
% 10.34/3.49  tff(c_6806, plain, (![A_19]: (k2_funct_1(k6_partfun1(A_19))=k6_partfun1(A_19) | k6_partfun1(k2_relat_1(k6_partfun1(A_19)))!=k6_partfun1(A_19) | k2_relat_1(k6_partfun1(A_19))!=k1_relat_1(k6_partfun1(A_19)) | ~v2_funct_1(k6_partfun1(A_19)) | ~v1_funct_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)) | ~v1_funct_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_323, c_6802])).
% 10.34/3.49  tff(c_6814, plain, (![A_19]: (k2_funct_1(k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_114, c_113, c_114, c_112, c_117, c_118, c_117, c_6806])).
% 10.34/3.49  tff(c_6694, plain, (![A_482, B_483]: (k2_funct_2(A_482, B_483)=k2_funct_1(B_483) | ~m1_subset_1(B_483, k1_zfmisc_1(k2_zfmisc_1(A_482, A_482))) | ~v3_funct_2(B_483, A_482, A_482) | ~v1_funct_2(B_483, A_482, A_482) | ~v1_funct_1(B_483))), inference(cnfTransformation, [status(thm)], [f_186])).
% 10.34/3.49  tff(c_6709, plain, (![A_58]: (k2_funct_2(A_58, k6_partfun1(A_58))=k2_funct_1(k6_partfun1(A_58)) | ~v3_funct_2(k6_partfun1(A_58), A_58, A_58) | ~v1_funct_2(k6_partfun1(A_58), A_58, A_58) | ~v1_funct_1(k6_partfun1(A_58)))), inference(resolution, [status(thm)], [c_80, c_6694])).
% 10.34/3.49  tff(c_6713, plain, (![A_58]: (k2_funct_2(A_58, k6_partfun1(A_58))=k2_funct_1(k6_partfun1(A_58)) | ~v3_funct_2(k6_partfun1(A_58), A_58, A_58) | ~v1_funct_2(k6_partfun1(A_58), A_58, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_6709])).
% 10.34/3.49  tff(c_16082, plain, (![A_756]: (k2_funct_2(A_756, k6_partfun1(A_756))=k6_partfun1(A_756) | ~v3_funct_2(k6_partfun1(A_756), A_756, A_756) | ~v1_funct_2(k6_partfun1(A_756), A_756, A_756))), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_6713])).
% 10.34/3.49  tff(c_16115, plain, (k2_funct_2('#skF_4', k6_partfun1('#skF_4'))=k6_partfun1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2(k6_partfun1('#skF_4'), '#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6149, c_16082])).
% 10.34/3.49  tff(c_16117, plain, (k2_funct_2('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6178, c_6149, c_6176, c_6149, c_6149, c_16115])).
% 10.34/3.49  tff(c_673, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_104, c_648])).
% 10.34/3.49  tff(c_6208, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6112, c_6161, c_673])).
% 10.34/3.49  tff(c_12, plain, (![B_8, A_7]: (~v1_xboole_0(B_8) | B_8=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.34/3.49  tff(c_6127, plain, (![A_7]: (A_7='#skF_2' | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_6113, c_12])).
% 10.34/3.49  tff(c_6367, plain, (![A_452]: (A_452='#skF_4' | ~v1_xboole_0(A_452))), inference(demodulation, [status(thm), theory('equality')], [c_6161, c_6127])).
% 10.34/3.49  tff(c_6374, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_6208, c_6367])).
% 10.34/3.49  tff(c_6172, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6161, c_6161, c_6161, c_92])).
% 10.34/3.49  tff(c_6607, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6374, c_6172])).
% 10.34/3.49  tff(c_16118, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16117, c_6607])).
% 10.34/3.49  tff(c_16121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9512, c_16118])).
% 10.34/3.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.34/3.49  
% 10.34/3.49  Inference rules
% 10.34/3.49  ----------------------
% 10.34/3.49  #Ref     : 0
% 10.34/3.49  #Sup     : 4070
% 10.34/3.49  #Fact    : 0
% 10.34/3.49  #Define  : 0
% 10.34/3.49  #Split   : 7
% 10.34/3.49  #Chain   : 0
% 10.34/3.49  #Close   : 0
% 10.34/3.49  
% 10.34/3.49  Ordering : KBO
% 10.34/3.49  
% 10.34/3.49  Simplification rules
% 10.34/3.49  ----------------------
% 10.34/3.49  #Subsume      : 765
% 10.34/3.49  #Demod        : 4242
% 10.34/3.49  #Tautology    : 2122
% 10.34/3.49  #SimpNegUnit  : 4
% 10.34/3.49  #BackRed      : 122
% 10.34/3.49  
% 10.34/3.49  #Partial instantiations: 0
% 10.34/3.49  #Strategies tried      : 1
% 10.34/3.49  
% 10.34/3.49  Timing (in seconds)
% 10.34/3.49  ----------------------
% 10.34/3.49  Preprocessing        : 0.45
% 10.34/3.49  Parsing              : 0.24
% 10.34/3.49  CNF conversion       : 0.03
% 10.34/3.49  Main loop            : 2.18
% 10.34/3.49  Inferencing          : 0.61
% 10.34/3.49  Reduction            : 0.83
% 10.34/3.49  Demodulation         : 0.62
% 10.34/3.49  BG Simplification    : 0.07
% 10.34/3.49  Subsumption          : 0.52
% 10.34/3.49  Abstraction          : 0.09
% 10.34/3.49  MUC search           : 0.00
% 10.34/3.49  Cooper               : 0.00
% 10.34/3.49  Total                : 2.68
% 10.34/3.49  Index Insertion      : 0.00
% 10.34/3.49  Index Deletion       : 0.00
% 10.34/3.49  Index Matching       : 0.00
% 10.34/3.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
