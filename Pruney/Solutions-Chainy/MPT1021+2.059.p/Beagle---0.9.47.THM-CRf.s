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
% DateTime   : Thu Dec  3 10:16:09 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  174 (8123 expanded)
%              Number of leaves         :   38 (3284 expanded)
%              Depth                    :   22
%              Number of atoms          :  440 (29736 expanded)
%              Number of equality atoms :   61 (1514 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_102,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_42,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k6_relat_1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_55,plain,(
    ! [A_16] : m1_subset_1(k6_partfun1(A_16),k1_zfmisc_1(k2_zfmisc_1(A_16,A_16))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_2118,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( r2_relset_1(A_168,B_169,C_170,C_170)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2128,plain,(
    ! [A_172,C_173] :
      ( r2_relset_1(A_172,A_172,C_173,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_172,A_172))) ) ),
    inference(resolution,[status(thm)],[c_55,c_2118])).

tff(c_2136,plain,(
    ! [A_16] : r2_relset_1(A_16,A_16,k6_partfun1(A_16),k6_partfun1(A_16)) ),
    inference(resolution,[status(thm)],[c_55,c_2128])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2172,plain,(
    ! [A_183,B_184] :
      ( k2_funct_2(A_183,B_184) = k2_funct_1(B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2178,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2172])).

tff(c_2186,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2178])).

tff(c_2153,plain,(
    ! [A_178,B_179] :
      ( v1_funct_1(k2_funct_2(A_178,B_179))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k2_zfmisc_1(A_178,A_178)))
      | ~ v3_funct_2(B_179,A_178,A_178)
      | ~ v1_funct_2(B_179,A_178,A_178)
      | ~ v1_funct_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2159,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2153])).

tff(c_2167,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2159])).

tff(c_2188,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2167])).

tff(c_69,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_2047,plain,(
    ! [C_155,A_156,B_157] :
      ( v2_funct_1(C_155)
      | ~ v3_funct_2(C_155,A_156,B_157)
      | ~ v1_funct_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2053,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2047])).

tff(c_2061,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2053])).

tff(c_2228,plain,(
    ! [A_198,B_199] :
      ( m1_subset_1(k2_funct_2(A_198,B_199),k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2258,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_2228])).

tff(c_2270,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2258])).

tff(c_16,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2321,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2270,c_16])).

tff(c_2211,plain,(
    ! [A_191,B_192] :
      ( v3_funct_2(k2_funct_2(A_191,B_192),A_191,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191)))
      | ~ v3_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2215,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2211])).

tff(c_2222,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2186,c_2215])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( v2_funct_1(C_19)
      | ~ v3_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2291,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2270,c_26])).

tff(c_2319,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2188,c_2222,c_2291])).

tff(c_2196,plain,(
    ! [A_186,B_187] :
      ( v1_funct_2(k2_funct_2(A_186,B_187),A_186,A_186)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2200,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2196])).

tff(c_2207,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2186,c_2200])).

tff(c_44,plain,(
    ! [A_31,B_32] :
      ( k1_relset_1(A_31,A_31,B_32) = A_31
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2285,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2270,c_44])).

tff(c_2313,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2188,c_2207,c_2285])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2320,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2270,c_18])).

tff(c_2400,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_2320])).

tff(c_14,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2035,plain,(
    ! [A_154] :
      ( k5_relat_1(A_154,k2_funct_1(A_154)) = k6_partfun1(k1_relat_1(A_154))
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_2752,plain,(
    ! [A_213] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_213))) = k5_relat_1(k2_funct_1(A_213),A_213)
      | ~ v2_funct_1(k2_funct_1(A_213))
      | ~ v1_funct_1(k2_funct_1(A_213))
      | ~ v1_relat_1(k2_funct_1(A_213))
      | ~ v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2035])).

tff(c_2809,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2400,c_2752])).

tff(c_2823,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_2061,c_2321,c_2188,c_2319,c_2809])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2326,plain,(
    ! [A_200,F_203,D_204,B_205,E_202,C_201] :
      ( k1_partfun1(A_200,B_205,C_201,D_204,E_202,F_203) = k5_relat_1(E_202,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_201,D_204)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_205)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2334,plain,(
    ! [A_200,B_205,E_202] :
      ( k1_partfun1(A_200,B_205,'#skF_2','#skF_2',E_202,'#skF_3') = k5_relat_1(E_202,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_205)))
      | ~ v1_funct_1(E_202) ) ),
    inference(resolution,[status(thm)],[c_48,c_2326])).

tff(c_2369,plain,(
    ! [A_206,B_207,E_208] :
      ( k1_partfun1(A_206,B_207,'#skF_2','#skF_2',E_208,'#skF_3') = k5_relat_1(E_208,'#skF_3')
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_1(E_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2334])).

tff(c_3199,plain,(
    ! [A_222,B_223] :
      ( k1_partfun1(A_222,A_222,'#skF_2','#skF_2',k2_funct_2(A_222,B_223),'#skF_3') = k5_relat_1(k2_funct_2(A_222,B_223),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_222,B_223))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(resolution,[status(thm)],[c_30,c_2369])).

tff(c_3211,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_3199])).

tff(c_3226,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2188,c_2186,c_2823,c_2186,c_2186,c_3211])).

tff(c_237,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_relset_1(A_65,B_66,C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_247,plain,(
    ! [A_69,C_70] :
      ( r2_relset_1(A_69,A_69,C_70,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,A_69))) ) ),
    inference(resolution,[status(thm)],[c_55,c_237])).

tff(c_255,plain,(
    ! [A_16] : r2_relset_1(A_16,A_16,k6_partfun1(A_16),k6_partfun1(A_16)) ),
    inference(resolution,[status(thm)],[c_55,c_247])).

tff(c_166,plain,(
    ! [C_52,A_53,B_54] :
      ( v2_funct_1(C_52)
      | ~ v3_funct_2(C_52,A_53,B_54)
      | ~ v1_funct_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_172,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_166])).

tff(c_180,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_172])).

tff(c_293,plain,(
    ! [A_83,B_84] :
      ( k2_funct_2(A_83,B_84) = k2_funct_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_299,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_293])).

tff(c_307,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_299])).

tff(c_406,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_funct_2(A_96,B_97),k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_436,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_406])).

tff(c_448,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_436])).

tff(c_499,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_16])).

tff(c_258,plain,(
    ! [A_71,B_72] :
      ( v1_funct_1(k2_funct_2(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_zfmisc_1(A_71,A_71)))
      | ~ v3_funct_2(B_72,A_71,A_71)
      | ~ v1_funct_2(B_72,A_71,A_71)
      | ~ v1_funct_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_264,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_258])).

tff(c_272,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_264])).

tff(c_309,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_272])).

tff(c_315,plain,(
    ! [A_85,B_86] :
      ( v3_funct_2(k2_funct_2(A_85,B_86),A_85,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_319,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_315])).

tff(c_326,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_307,c_319])).

tff(c_469,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_26])).

tff(c_497,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_326,c_469])).

tff(c_332,plain,(
    ! [A_92,B_93] :
      ( v1_funct_2(k2_funct_2(A_92,B_93),A_92,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_336,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_332])).

tff(c_343,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_307,c_336])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( k2_funct_2(A_28,B_29) = k2_funct_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v3_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_2(B_29,A_28,A_28)
      | ~ v1_funct_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_455,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_40])).

tff(c_484,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_455])).

tff(c_588,plain,(
    ! [A_107,B_108] :
      ( v1_relat_1(k2_funct_2(A_107,B_108))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ v3_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_406,c_16])).

tff(c_591,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_588])).

tff(c_607,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_484,c_591])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k2_funct_2(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_460,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_36])).

tff(c_488,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_460])).

tff(c_526,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_488])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( v3_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_452,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_32])).

tff(c_481,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_452])).

tff(c_572,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_481])).

tff(c_530,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_30])).

tff(c_534,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_448,c_530])).

tff(c_715,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_534,c_26])).

tff(c_755,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_572,c_715])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( v1_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_450,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_34])).

tff(c_478,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_450])).

tff(c_525,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_478])).

tff(c_709,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_534,c_44])).

tff(c_749,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_525,c_709])).

tff(c_1108,plain,(
    ! [A_117,B_118] :
      ( k1_relset_1(A_117,A_117,k2_funct_2(A_117,B_118)) = k1_relat_1(k2_funct_2(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_406,c_18])).

tff(c_1112,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_1108])).

tff(c_1127,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_749,c_484,c_484,c_1112])).

tff(c_701,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_534,c_40])).

tff(c_742,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_525,c_572,c_701])).

tff(c_843,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_742])).

tff(c_849,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_180,c_307,c_843])).

tff(c_10,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [A_50] :
      ( k5_relat_1(k2_funct_1(A_50),A_50) = k6_partfun1(k2_relat_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_151,plain,(
    ! [A_5] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_5))) = k5_relat_1(A_5,k2_funct_1(A_5))
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_142])).

tff(c_942,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_151])).

tff(c_976,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_526,c_755,c_499,c_849,c_309,c_849,c_497,c_849,c_849,c_942])).

tff(c_154,plain,(
    ! [A_51] :
      ( k5_relat_1(A_51,k2_funct_1(A_51)) = k6_partfun1(k1_relat_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_163,plain,(
    ! [A_5] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_5))) = k5_relat_1(k2_funct_1(A_5),A_5)
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_154])).

tff(c_1261,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_163])).

tff(c_1277,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_309,c_497,c_607,c_526,c_755,c_1127,c_1261])).

tff(c_1293,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1277,c_151])).

tff(c_1338,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_180,c_499,c_309,c_497,c_1293])).

tff(c_500,plain,(
    ! [C_99,A_98,E_100,B_103,F_101,D_102] :
      ( k1_partfun1(A_98,B_103,C_99,D_102,E_100,F_101) = k5_relat_1(E_100,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_99,D_102)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_103)))
      | ~ v1_funct_1(E_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_502,plain,(
    ! [A_98,B_103,E_100] :
      ( k1_partfun1(A_98,B_103,'#skF_2','#skF_2',E_100,k2_funct_1('#skF_3')) = k5_relat_1(E_100,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_103)))
      | ~ v1_funct_1(E_100) ) ),
    inference(resolution,[status(thm)],[c_448,c_500])).

tff(c_1907,plain,(
    ! [A_139,B_140,E_141] :
      ( k1_partfun1(A_139,B_140,'#skF_2','#skF_2',E_141,k2_funct_1('#skF_3')) = k5_relat_1(E_141,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(E_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_502])).

tff(c_1937,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1907])).

tff(c_1957,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1338,c_1937])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_83,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_310,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_83])).

tff(c_1959,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1957,c_310])).

tff(c_1962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1959])).

tff(c_1963,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2190,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_1963])).

tff(c_3259,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_2190])).

tff(c_3262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_3259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:18:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.06  
% 5.67/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.06  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.67/2.06  
% 5.67/2.06  %Foreground sorts:
% 5.67/2.06  
% 5.67/2.06  
% 5.67/2.06  %Background operators:
% 5.67/2.06  
% 5.67/2.06  
% 5.67/2.06  %Foreground operators:
% 5.67/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.67/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.67/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.67/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.06  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.67/2.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.67/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.67/2.06  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.67/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.67/2.06  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.67/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.67/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.06  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.67/2.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.67/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.67/2.06  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.67/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.67/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.67/2.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.67/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.06  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.67/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.67/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.67/2.06  
% 5.78/2.09  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.78/2.09  tff(f_74, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.78/2.09  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.78/2.09  tff(f_145, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.78/2.09  tff(f_122, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.78/2.09  tff(f_102, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.78/2.09  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.78/2.09  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.78/2.09  tff(f_132, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.78/2.09  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.78/2.09  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.78/2.09  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.78/2.09  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.78/2.09  tff(c_42, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.78/2.09  tff(c_22, plain, (![A_16]: (m1_subset_1(k6_relat_1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.78/2.09  tff(c_55, plain, (![A_16]: (m1_subset_1(k6_partfun1(A_16), k1_zfmisc_1(k2_zfmisc_1(A_16, A_16))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 5.78/2.09  tff(c_2118, plain, (![A_168, B_169, C_170, D_171]: (r2_relset_1(A_168, B_169, C_170, C_170) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.78/2.09  tff(c_2128, plain, (![A_172, C_173]: (r2_relset_1(A_172, A_172, C_173, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_172, A_172))))), inference(resolution, [status(thm)], [c_55, c_2118])).
% 5.78/2.09  tff(c_2136, plain, (![A_16]: (r2_relset_1(A_16, A_16, k6_partfun1(A_16), k6_partfun1(A_16)))), inference(resolution, [status(thm)], [c_55, c_2128])).
% 5.78/2.09  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.78/2.09  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.78/2.09  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.78/2.09  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.78/2.09  tff(c_2172, plain, (![A_183, B_184]: (k2_funct_2(A_183, B_184)=k2_funct_1(B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.78/2.09  tff(c_2178, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2172])).
% 5.78/2.09  tff(c_2186, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2178])).
% 5.78/2.09  tff(c_2153, plain, (![A_178, B_179]: (v1_funct_1(k2_funct_2(A_178, B_179)) | ~m1_subset_1(B_179, k1_zfmisc_1(k2_zfmisc_1(A_178, A_178))) | ~v3_funct_2(B_179, A_178, A_178) | ~v1_funct_2(B_179, A_178, A_178) | ~v1_funct_1(B_179))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_2159, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2153])).
% 5.78/2.09  tff(c_2167, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2159])).
% 5.78/2.09  tff(c_2188, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2167])).
% 5.78/2.09  tff(c_69, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.78/2.09  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_69])).
% 5.78/2.09  tff(c_2047, plain, (![C_155, A_156, B_157]: (v2_funct_1(C_155) | ~v3_funct_2(C_155, A_156, B_157) | ~v1_funct_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.78/2.09  tff(c_2053, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2047])).
% 5.78/2.09  tff(c_2061, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2053])).
% 5.78/2.09  tff(c_2228, plain, (![A_198, B_199]: (m1_subset_1(k2_funct_2(A_198, B_199), k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_2258, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2186, c_2228])).
% 5.78/2.09  tff(c_2270, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_2258])).
% 5.78/2.09  tff(c_16, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.78/2.09  tff(c_2321, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2270, c_16])).
% 5.78/2.09  tff(c_2211, plain, (![A_191, B_192]: (v3_funct_2(k2_funct_2(A_191, B_192), A_191, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))) | ~v3_funct_2(B_192, A_191, A_191) | ~v1_funct_2(B_192, A_191, A_191) | ~v1_funct_1(B_192))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_2215, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2211])).
% 5.78/2.09  tff(c_2222, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2186, c_2215])).
% 5.78/2.09  tff(c_26, plain, (![C_19, A_17, B_18]: (v2_funct_1(C_19) | ~v3_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.78/2.09  tff(c_2291, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2270, c_26])).
% 5.78/2.09  tff(c_2319, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2188, c_2222, c_2291])).
% 5.78/2.09  tff(c_2196, plain, (![A_186, B_187]: (v1_funct_2(k2_funct_2(A_186, B_187), A_186, A_186) | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_187, A_186, A_186) | ~v1_funct_2(B_187, A_186, A_186) | ~v1_funct_1(B_187))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_2200, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2196])).
% 5.78/2.09  tff(c_2207, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2186, c_2200])).
% 5.78/2.09  tff(c_44, plain, (![A_31, B_32]: (k1_relset_1(A_31, A_31, B_32)=A_31 | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.78/2.09  tff(c_2285, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2270, c_44])).
% 5.78/2.09  tff(c_2313, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2188, c_2207, c_2285])).
% 5.78/2.09  tff(c_18, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.78/2.09  tff(c_2320, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2270, c_18])).
% 5.78/2.09  tff(c_2400, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_2320])).
% 5.78/2.09  tff(c_14, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.78/2.09  tff(c_12, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.78/2.09  tff(c_2035, plain, (![A_154]: (k5_relat_1(A_154, k2_funct_1(A_154))=k6_partfun1(k1_relat_1(A_154)) | ~v2_funct_1(A_154) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 5.78/2.09  tff(c_2752, plain, (![A_213]: (k6_partfun1(k1_relat_1(k2_funct_1(A_213)))=k5_relat_1(k2_funct_1(A_213), A_213) | ~v2_funct_1(k2_funct_1(A_213)) | ~v1_funct_1(k2_funct_1(A_213)) | ~v1_relat_1(k2_funct_1(A_213)) | ~v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2035])).
% 5.78/2.09  tff(c_2809, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2400, c_2752])).
% 5.78/2.09  tff(c_2823, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_2061, c_2321, c_2188, c_2319, c_2809])).
% 5.78/2.09  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_2326, plain, (![A_200, F_203, D_204, B_205, E_202, C_201]: (k1_partfun1(A_200, B_205, C_201, D_204, E_202, F_203)=k5_relat_1(E_202, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_201, D_204))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_205))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.78/2.09  tff(c_2334, plain, (![A_200, B_205, E_202]: (k1_partfun1(A_200, B_205, '#skF_2', '#skF_2', E_202, '#skF_3')=k5_relat_1(E_202, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_205))) | ~v1_funct_1(E_202))), inference(resolution, [status(thm)], [c_48, c_2326])).
% 5.78/2.09  tff(c_2369, plain, (![A_206, B_207, E_208]: (k1_partfun1(A_206, B_207, '#skF_2', '#skF_2', E_208, '#skF_3')=k5_relat_1(E_208, '#skF_3') | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_1(E_208))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2334])).
% 5.78/2.09  tff(c_3199, plain, (![A_222, B_223]: (k1_partfun1(A_222, A_222, '#skF_2', '#skF_2', k2_funct_2(A_222, B_223), '#skF_3')=k5_relat_1(k2_funct_2(A_222, B_223), '#skF_3') | ~v1_funct_1(k2_funct_2(A_222, B_223)) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(resolution, [status(thm)], [c_30, c_2369])).
% 5.78/2.09  tff(c_3211, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_3199])).
% 5.78/2.09  tff(c_3226, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2188, c_2186, c_2823, c_2186, c_2186, c_3211])).
% 5.78/2.09  tff(c_237, plain, (![A_65, B_66, C_67, D_68]: (r2_relset_1(A_65, B_66, C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.78/2.09  tff(c_247, plain, (![A_69, C_70]: (r2_relset_1(A_69, A_69, C_70, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))))), inference(resolution, [status(thm)], [c_55, c_237])).
% 5.78/2.09  tff(c_255, plain, (![A_16]: (r2_relset_1(A_16, A_16, k6_partfun1(A_16), k6_partfun1(A_16)))), inference(resolution, [status(thm)], [c_55, c_247])).
% 5.78/2.09  tff(c_166, plain, (![C_52, A_53, B_54]: (v2_funct_1(C_52) | ~v3_funct_2(C_52, A_53, B_54) | ~v1_funct_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.78/2.09  tff(c_172, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_166])).
% 5.78/2.09  tff(c_180, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_172])).
% 5.78/2.09  tff(c_293, plain, (![A_83, B_84]: (k2_funct_2(A_83, B_84)=k2_funct_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.78/2.09  tff(c_299, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_293])).
% 5.78/2.09  tff(c_307, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_299])).
% 5.78/2.09  tff(c_406, plain, (![A_96, B_97]: (m1_subset_1(k2_funct_2(A_96, B_97), k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_436, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_307, c_406])).
% 5.78/2.09  tff(c_448, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_436])).
% 5.78/2.09  tff(c_499, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_16])).
% 5.78/2.09  tff(c_258, plain, (![A_71, B_72]: (v1_funct_1(k2_funct_2(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_zfmisc_1(A_71, A_71))) | ~v3_funct_2(B_72, A_71, A_71) | ~v1_funct_2(B_72, A_71, A_71) | ~v1_funct_1(B_72))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_264, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_258])).
% 5.78/2.09  tff(c_272, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_264])).
% 5.78/2.09  tff(c_309, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_272])).
% 5.78/2.09  tff(c_315, plain, (![A_85, B_86]: (v3_funct_2(k2_funct_2(A_85, B_86), A_85, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_319, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_315])).
% 5.78/2.09  tff(c_326, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_307, c_319])).
% 5.78/2.09  tff(c_469, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_26])).
% 5.78/2.09  tff(c_497, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_326, c_469])).
% 5.78/2.09  tff(c_332, plain, (![A_92, B_93]: (v1_funct_2(k2_funct_2(A_92, B_93), A_92, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_336, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_332])).
% 5.78/2.09  tff(c_343, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_307, c_336])).
% 5.78/2.09  tff(c_40, plain, (![A_28, B_29]: (k2_funct_2(A_28, B_29)=k2_funct_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v3_funct_2(B_29, A_28, A_28) | ~v1_funct_2(B_29, A_28, A_28) | ~v1_funct_1(B_29))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.78/2.09  tff(c_455, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_40])).
% 5.78/2.09  tff(c_484, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_455])).
% 5.78/2.09  tff(c_588, plain, (![A_107, B_108]: (v1_relat_1(k2_funct_2(A_107, B_108)) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~v3_funct_2(B_108, A_107, A_107) | ~v1_funct_2(B_108, A_107, A_107) | ~v1_funct_1(B_108))), inference(resolution, [status(thm)], [c_406, c_16])).
% 5.78/2.09  tff(c_591, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_588])).
% 5.78/2.09  tff(c_607, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_484, c_591])).
% 5.78/2.09  tff(c_36, plain, (![A_20, B_21]: (v1_funct_1(k2_funct_2(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_460, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_36])).
% 5.78/2.09  tff(c_488, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_460])).
% 5.78/2.09  tff(c_526, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_488])).
% 5.78/2.09  tff(c_32, plain, (![A_20, B_21]: (v3_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_452, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_32])).
% 5.78/2.09  tff(c_481, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_452])).
% 5.78/2.09  tff(c_572, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_481])).
% 5.78/2.09  tff(c_530, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_484, c_30])).
% 5.78/2.09  tff(c_534, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_448, c_530])).
% 5.78/2.09  tff(c_715, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_534, c_26])).
% 5.78/2.09  tff(c_755, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_572, c_715])).
% 5.78/2.09  tff(c_34, plain, (![A_20, B_21]: (v1_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.78/2.09  tff(c_450, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_34])).
% 5.78/2.09  tff(c_478, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_450])).
% 5.78/2.09  tff(c_525, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_484, c_478])).
% 5.78/2.09  tff(c_709, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_534, c_44])).
% 5.78/2.09  tff(c_749, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_526, c_525, c_709])).
% 5.78/2.09  tff(c_1108, plain, (![A_117, B_118]: (k1_relset_1(A_117, A_117, k2_funct_2(A_117, B_118))=k1_relat_1(k2_funct_2(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(resolution, [status(thm)], [c_406, c_18])).
% 5.78/2.09  tff(c_1112, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_2('#skF_2', k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_1108])).
% 5.78/2.09  tff(c_1127, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_749, c_484, c_484, c_1112])).
% 5.78/2.09  tff(c_701, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_534, c_40])).
% 5.78/2.09  tff(c_742, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_525, c_572, c_701])).
% 5.78/2.09  tff(c_843, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_742])).
% 5.78/2.09  tff(c_849, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_180, c_307, c_843])).
% 5.78/2.09  tff(c_10, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.78/2.09  tff(c_142, plain, (![A_50]: (k5_relat_1(k2_funct_1(A_50), A_50)=k6_partfun1(k2_relat_1(A_50)) | ~v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 5.78/2.09  tff(c_151, plain, (![A_5]: (k6_partfun1(k2_relat_1(k2_funct_1(A_5)))=k5_relat_1(A_5, k2_funct_1(A_5)) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_142])).
% 5.78/2.09  tff(c_942, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_849, c_151])).
% 5.78/2.09  tff(c_976, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_526, c_755, c_499, c_849, c_309, c_849, c_497, c_849, c_849, c_942])).
% 5.78/2.09  tff(c_154, plain, (![A_51]: (k5_relat_1(A_51, k2_funct_1(A_51))=k6_partfun1(k1_relat_1(A_51)) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 5.78/2.09  tff(c_163, plain, (![A_5]: (k6_partfun1(k1_relat_1(k2_funct_1(A_5)))=k5_relat_1(k2_funct_1(A_5), A_5) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_154])).
% 5.78/2.09  tff(c_1261, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_976, c_163])).
% 5.78/2.09  tff(c_1277, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_309, c_497, c_607, c_526, c_755, c_1127, c_1261])).
% 5.78/2.09  tff(c_1293, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1277, c_151])).
% 5.78/2.09  tff(c_1338, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_180, c_499, c_309, c_497, c_1293])).
% 5.78/2.09  tff(c_500, plain, (![C_99, A_98, E_100, B_103, F_101, D_102]: (k1_partfun1(A_98, B_103, C_99, D_102, E_100, F_101)=k5_relat_1(E_100, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_99, D_102))) | ~v1_funct_1(F_101) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_103))) | ~v1_funct_1(E_100))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.78/2.09  tff(c_502, plain, (![A_98, B_103, E_100]: (k1_partfun1(A_98, B_103, '#skF_2', '#skF_2', E_100, k2_funct_1('#skF_3'))=k5_relat_1(E_100, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_103))) | ~v1_funct_1(E_100))), inference(resolution, [status(thm)], [c_448, c_500])).
% 5.78/2.09  tff(c_1907, plain, (![A_139, B_140, E_141]: (k1_partfun1(A_139, B_140, '#skF_2', '#skF_2', E_141, k2_funct_1('#skF_3'))=k5_relat_1(E_141, k2_funct_1('#skF_3')) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_1(E_141))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_502])).
% 5.78/2.09  tff(c_1937, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1907])).
% 5.78/2.09  tff(c_1957, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1338, c_1937])).
% 5.78/2.09  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.78/2.09  tff(c_83, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.78/2.09  tff(c_310, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_83])).
% 5.78/2.09  tff(c_1959, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1957, c_310])).
% 5.78/2.09  tff(c_1962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_1959])).
% 5.78/2.09  tff(c_1963, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 5.78/2.09  tff(c_2190, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_1963])).
% 5.78/2.09  tff(c_3259, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_2190])).
% 5.78/2.09  tff(c_3262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2136, c_3259])).
% 5.78/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.78/2.09  
% 5.78/2.09  Inference rules
% 5.78/2.09  ----------------------
% 5.78/2.09  #Ref     : 0
% 5.78/2.09  #Sup     : 777
% 5.78/2.09  #Fact    : 0
% 5.78/2.09  #Define  : 0
% 5.78/2.09  #Split   : 3
% 5.78/2.09  #Chain   : 0
% 5.78/2.09  #Close   : 0
% 5.78/2.09  
% 5.78/2.09  Ordering : KBO
% 5.78/2.09  
% 5.78/2.09  Simplification rules
% 5.78/2.09  ----------------------
% 5.78/2.09  #Subsume      : 92
% 5.78/2.09  #Demod        : 1427
% 5.78/2.09  #Tautology    : 332
% 5.78/2.09  #SimpNegUnit  : 0
% 5.78/2.09  #BackRed      : 31
% 5.78/2.09  
% 5.78/2.09  #Partial instantiations: 0
% 5.78/2.09  #Strategies tried      : 1
% 5.78/2.09  
% 5.78/2.09  Timing (in seconds)
% 5.78/2.09  ----------------------
% 5.78/2.09  Preprocessing        : 0.34
% 5.78/2.09  Parsing              : 0.18
% 5.78/2.09  CNF conversion       : 0.02
% 5.78/2.09  Main loop            : 0.95
% 5.78/2.09  Inferencing          : 0.32
% 5.78/2.09  Reduction            : 0.37
% 5.78/2.09  Demodulation         : 0.28
% 5.78/2.09  BG Simplification    : 0.04
% 5.78/2.09  Subsumption          : 0.15
% 5.78/2.09  Abstraction          : 0.05
% 5.78/2.09  MUC search           : 0.00
% 5.78/2.09  Cooper               : 0.00
% 5.78/2.09  Total                : 1.35
% 5.78/2.09  Index Insertion      : 0.00
% 5.78/2.09  Index Deletion       : 0.00
% 5.78/2.09  Index Matching       : 0.00
% 5.78/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
