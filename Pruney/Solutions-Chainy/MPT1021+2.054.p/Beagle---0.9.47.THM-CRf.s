%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:08 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  177 (8024 expanded)
%              Number of leaves         :   39 (3244 expanded)
%              Depth                    :   22
%              Number of atoms          :  442 (29361 expanded)
%              Number of equality atoms :   61 (1493 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_subset_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff(f_131,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_81,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_109,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_44,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_24])).

tff(c_2061,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( r2_relset_1(A_166,B_167,C_168,C_168)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2098,plain,(
    ! [A_172,C_173] :
      ( r2_relset_1(A_172,A_172,C_173,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_172,A_172))) ) ),
    inference(resolution,[status(thm)],[c_57,c_2061])).

tff(c_2106,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_57,c_2098])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2144,plain,(
    ! [A_186,B_187] :
      ( k2_funct_2(A_186,B_187) = k2_funct_1(B_187)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_2(B_187,A_186,A_186)
      | ~ v1_funct_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2150,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2144])).

tff(c_2158,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2150])).

tff(c_2126,plain,(
    ! [A_181,B_182] :
      ( v1_funct_1(k2_funct_2(A_181,B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_zfmisc_1(A_181,A_181)))
      | ~ v3_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2132,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2126])).

tff(c_2140,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2132])).

tff(c_2160,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2140])).

tff(c_1924,plain,(
    ! [C_142,A_143,B_144] :
      ( v1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1936,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1924])).

tff(c_2027,plain,(
    ! [C_158,A_159,B_160] :
      ( v2_funct_1(C_158)
      | ~ v3_funct_2(C_158,A_159,B_160)
      | ~ v1_funct_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2033,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2027])).

tff(c_2041,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2033])).

tff(c_2259,plain,(
    ! [A_200,B_201] :
      ( m1_subset_1(k2_funct_2(A_200,B_201),k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ v3_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2289,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2158,c_2259])).

tff(c_2301,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2289])).

tff(c_18,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2352,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2301,c_18])).

tff(c_2183,plain,(
    ! [A_194,B_195] :
      ( v3_funct_2(k2_funct_2(A_194,B_195),A_194,A_194)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_195,A_194,A_194)
      | ~ v1_funct_2(B_195,A_194,A_194)
      | ~ v1_funct_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2187,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2183])).

tff(c_2194,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2158,c_2187])).

tff(c_28,plain,(
    ! [C_20,A_18,B_19] :
      ( v2_funct_1(C_20)
      | ~ v3_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2322,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2301,c_28])).

tff(c_2350,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_2194,c_2322])).

tff(c_2168,plain,(
    ! [A_189,B_190] :
      ( v1_funct_2(k2_funct_2(A_189,B_190),A_189,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2172,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2168])).

tff(c_2179,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2158,c_2172])).

tff(c_46,plain,(
    ! [A_32,B_33] :
      ( k1_relset_1(A_32,A_32,B_33) = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2316,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2301,c_46])).

tff(c_2344,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_2179,c_2316])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2351,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2301,c_20])).

tff(c_2431,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_2351])).

tff(c_16,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2015,plain,(
    ! [A_157] :
      ( k5_relat_1(A_157,k2_funct_1(A_157)) = k6_partfun1(k1_relat_1(A_157))
      | ~ v2_funct_1(A_157)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_2024,plain,(
    ! [A_6] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_6))) = k5_relat_1(k2_funct_1(A_6),A_6)
      | ~ v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2015])).

tff(c_2435,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2431,c_2024])).

tff(c_2439,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_56,c_2041,c_2352,c_2160,c_2350,c_2435])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_funct_2(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2357,plain,(
    ! [A_207,F_203,B_205,C_202,E_204,D_206] :
      ( k1_partfun1(A_207,B_205,C_202,D_206,E_204,F_203) = k5_relat_1(E_204,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_202,D_206)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205)))
      | ~ v1_funct_1(E_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2365,plain,(
    ! [A_207,B_205,E_204] :
      ( k1_partfun1(A_207,B_205,'#skF_2','#skF_2',E_204,'#skF_3') = k5_relat_1(E_204,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205)))
      | ~ v1_funct_1(E_204) ) ),
    inference(resolution,[status(thm)],[c_50,c_2357])).

tff(c_2400,plain,(
    ! [A_208,B_209,E_210] :
      ( k1_partfun1(A_208,B_209,'#skF_2','#skF_2',E_210,'#skF_3') = k5_relat_1(E_210,'#skF_3')
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ v1_funct_1(E_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2365])).

tff(c_3172,plain,(
    ! [A_224,B_225] :
      ( k1_partfun1(A_224,A_224,'#skF_2','#skF_2',k2_funct_2(A_224,B_225),'#skF_3') = k5_relat_1(k2_funct_2(A_224,B_225),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_224,B_225))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(k2_zfmisc_1(A_224,A_224)))
      | ~ v3_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_2(B_225,A_224,A_224)
      | ~ v1_funct_1(B_225) ) ),
    inference(resolution,[status(thm)],[c_32,c_2400])).

tff(c_3184,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3172])).

tff(c_3199,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2160,c_2158,c_2439,c_2158,c_2158,c_3184])).

tff(c_211,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( r2_relset_1(A_63,B_64,C_65,C_65)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_221,plain,(
    ! [A_67,C_68] :
      ( r2_relset_1(A_67,A_67,C_68,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,A_67))) ) ),
    inference(resolution,[status(thm)],[c_57,c_211])).

tff(c_229,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_57,c_221])).

tff(c_75,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_75])).

tff(c_178,plain,(
    ! [C_56,A_57,B_58] :
      ( v2_funct_1(C_56)
      | ~ v3_funct_2(C_56,A_57,B_58)
      | ~ v1_funct_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_184,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_178])).

tff(c_192,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_184])).

tff(c_295,plain,(
    ! [A_84,B_85] :
      ( k2_funct_2(A_84,B_85) = k2_funct_1(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84)))
      | ~ v3_funct_2(B_85,A_84,A_84)
      | ~ v1_funct_2(B_85,A_84,A_84)
      | ~ v1_funct_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_301,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_295])).

tff(c_309,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_301])).

tff(c_349,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k2_funct_2(A_97,B_98),k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_379,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_349])).

tff(c_391,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_379])).

tff(c_442,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_18])).

tff(c_274,plain,(
    ! [A_76,B_77] :
      ( v1_funct_1(k2_funct_2(A_76,B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_zfmisc_1(A_76,A_76)))
      | ~ v3_funct_2(B_77,A_76,A_76)
      | ~ v1_funct_2(B_77,A_76,A_76)
      | ~ v1_funct_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_280,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_274])).

tff(c_288,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_280])).

tff(c_311,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_288])).

tff(c_317,plain,(
    ! [A_86,B_87] :
      ( v3_funct_2(k2_funct_2(A_86,B_87),A_86,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_zfmisc_1(A_86,A_86)))
      | ~ v3_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_321,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_317])).

tff(c_328,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_309,c_321])).

tff(c_412,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_28])).

tff(c_440,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_328,c_412])).

tff(c_10,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [A_55] :
      ( k5_relat_1(k2_funct_1(A_55),A_55) = k6_partfun1(k2_relat_1(A_55))
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_175,plain,(
    ! [A_6] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_6))) = k5_relat_1(A_6,k2_funct_1(A_6))
      | ~ v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_166])).

tff(c_334,plain,(
    ! [A_93,B_94] :
      ( v1_funct_2(k2_funct_2(A_93,B_94),A_93,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_338,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_334])).

tff(c_345,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_309,c_338])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_398,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_42])).

tff(c_427,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_345,c_328,c_398])).

tff(c_526,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(k2_funct_2(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_349,c_18])).

tff(c_529,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_526])).

tff(c_545,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_345,c_328,c_427,c_529])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( v1_funct_1(k2_funct_2(A_21,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_401,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_38])).

tff(c_430,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_345,c_328,c_401])).

tff(c_469,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_430])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( v3_funct_2(k2_funct_2(A_21,B_22),A_21,A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_395,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_34])).

tff(c_424,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_345,c_328,c_395])).

tff(c_468,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_424])).

tff(c_473,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_32])).

tff(c_477,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_345,c_328,c_391,c_473])).

tff(c_585,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_28])).

tff(c_625,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_468,c_585])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( v1_funct_2(k2_funct_2(A_21,B_22),A_21,A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_393,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_391,c_36])).

tff(c_421,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_345,c_328,c_393])).

tff(c_515,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_421])).

tff(c_577,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_46])).

tff(c_618,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_515,c_577])).

tff(c_626,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_20])).

tff(c_1165,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_626])).

tff(c_571,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_42])).

tff(c_612,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_515,c_468,c_571])).

tff(c_840,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_612])).

tff(c_846,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_56,c_192,c_309,c_840])).

tff(c_1021,plain,(
    ! [A_118] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_118))) = k5_relat_1(A_118,k2_funct_1(A_118))
      | ~ v2_funct_1(k2_funct_1(A_118))
      | ~ v1_funct_1(k2_funct_1(A_118))
      | ~ v1_relat_1(k2_funct_1(A_118))
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_166])).

tff(c_1083,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_1021])).

tff(c_1099,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_469,c_625,c_442,c_846,c_311,c_846,c_440,c_846,c_846,c_1083])).

tff(c_154,plain,(
    ! [A_54] :
      ( k5_relat_1(A_54,k2_funct_1(A_54)) = k6_partfun1(k1_relat_1(A_54))
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_163,plain,(
    ! [A_6] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_6))) = k5_relat_1(k2_funct_1(A_6),A_6)
      | ~ v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_154])).

tff(c_1183,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1099,c_163])).

tff(c_1199,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_311,c_440,c_545,c_469,c_625,c_1165,c_1183])).

tff(c_1257,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_1199])).

tff(c_1276,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_56,c_192,c_442,c_311,c_440,c_1257])).

tff(c_443,plain,(
    ! [C_99,D_103,B_102,A_104,F_100,E_101] :
      ( k1_partfun1(A_104,B_102,C_99,D_103,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_99,D_103)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_445,plain,(
    ! [A_104,B_102,E_101] :
      ( k1_partfun1(A_104,B_102,'#skF_2','#skF_2',E_101,k2_funct_1('#skF_3')) = k5_relat_1(E_101,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(resolution,[status(thm)],[c_391,c_443])).

tff(c_1865,plain,(
    ! [A_138,B_139,E_140] :
      ( k1_partfun1(A_138,B_139,'#skF_2','#skF_2',E_140,k2_funct_1('#skF_3')) = k5_relat_1(E_140,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_445])).

tff(c_1895,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1865])).

tff(c_1915,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1276,c_1895])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_73,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_312,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_73])).

tff(c_1917,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_312])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_1917])).

tff(c_1921,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2162,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_1921])).

tff(c_3231,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3199,c_2162])).

tff(c_3234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_3231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.99  
% 5.19/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.99  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_subset_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.19/1.99  
% 5.19/1.99  %Foreground sorts:
% 5.19/1.99  
% 5.19/1.99  
% 5.19/1.99  %Background operators:
% 5.19/1.99  
% 5.19/1.99  
% 5.19/1.99  %Foreground operators:
% 5.19/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.19/1.99  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.19/1.99  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.19/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.19/1.99  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.19/1.99  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.19/1.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.19/1.99  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.19/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.19/1.99  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.19/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.19/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.19/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.19/1.99  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.19/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.19/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/1.99  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.19/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.19/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.19/1.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.19/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.99  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.19/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.19/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/1.99  
% 5.55/2.02  tff(f_131, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.55/2.02  tff(f_81, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.55/2.02  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.55/2.02  tff(f_152, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.55/2.02  tff(f_129, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.55/2.02  tff(f_109, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.55/2.02  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.55/2.02  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.55/2.02  tff(f_139, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.55/2.02  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.55/2.02  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.55/2.02  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.55/2.02  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.55/2.02  tff(c_44, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.55/2.02  tff(c_24, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.55/2.02  tff(c_57, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_24])).
% 5.55/2.02  tff(c_2061, plain, (![A_166, B_167, C_168, D_169]: (r2_relset_1(A_166, B_167, C_168, C_168) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.55/2.02  tff(c_2098, plain, (![A_172, C_173]: (r2_relset_1(A_172, A_172, C_173, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_172, A_172))))), inference(resolution, [status(thm)], [c_57, c_2061])).
% 5.55/2.02  tff(c_2106, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_57, c_2098])).
% 5.55/2.02  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.55/2.02  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.55/2.02  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.55/2.02  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.55/2.02  tff(c_2144, plain, (![A_186, B_187]: (k2_funct_2(A_186, B_187)=k2_funct_1(B_187) | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_187, A_186, A_186) | ~v1_funct_2(B_187, A_186, A_186) | ~v1_funct_1(B_187))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.55/2.02  tff(c_2150, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2144])).
% 5.55/2.02  tff(c_2158, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2150])).
% 5.55/2.02  tff(c_2126, plain, (![A_181, B_182]: (v1_funct_1(k2_funct_2(A_181, B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))) | ~v3_funct_2(B_182, A_181, A_181) | ~v1_funct_2(B_182, A_181, A_181) | ~v1_funct_1(B_182))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_2132, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2126])).
% 5.55/2.02  tff(c_2140, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2132])).
% 5.55/2.02  tff(c_2160, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2140])).
% 5.55/2.02  tff(c_1924, plain, (![C_142, A_143, B_144]: (v1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.55/2.02  tff(c_1936, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1924])).
% 5.55/2.02  tff(c_2027, plain, (![C_158, A_159, B_160]: (v2_funct_1(C_158) | ~v3_funct_2(C_158, A_159, B_160) | ~v1_funct_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.55/2.02  tff(c_2033, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2027])).
% 5.55/2.02  tff(c_2041, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2033])).
% 5.55/2.02  tff(c_2259, plain, (![A_200, B_201]: (m1_subset_1(k2_funct_2(A_200, B_201), k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~m1_subset_1(B_201, k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~v3_funct_2(B_201, A_200, A_200) | ~v1_funct_2(B_201, A_200, A_200) | ~v1_funct_1(B_201))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_2289, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2158, c_2259])).
% 5.55/2.02  tff(c_2301, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2289])).
% 5.55/2.02  tff(c_18, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.55/2.02  tff(c_2352, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2301, c_18])).
% 5.55/2.02  tff(c_2183, plain, (![A_194, B_195]: (v3_funct_2(k2_funct_2(A_194, B_195), A_194, A_194) | ~m1_subset_1(B_195, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_195, A_194, A_194) | ~v1_funct_2(B_195, A_194, A_194) | ~v1_funct_1(B_195))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_2187, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2183])).
% 5.55/2.02  tff(c_2194, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2158, c_2187])).
% 5.55/2.02  tff(c_28, plain, (![C_20, A_18, B_19]: (v2_funct_1(C_20) | ~v3_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.55/2.02  tff(c_2322, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2301, c_28])).
% 5.55/2.02  tff(c_2350, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_2194, c_2322])).
% 5.55/2.02  tff(c_2168, plain, (![A_189, B_190]: (v1_funct_2(k2_funct_2(A_189, B_190), A_189, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_2172, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2168])).
% 5.55/2.02  tff(c_2179, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2158, c_2172])).
% 5.55/2.02  tff(c_46, plain, (![A_32, B_33]: (k1_relset_1(A_32, A_32, B_33)=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.55/2.02  tff(c_2316, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2301, c_46])).
% 5.55/2.02  tff(c_2344, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_2179, c_2316])).
% 5.55/2.02  tff(c_20, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.55/2.02  tff(c_2351, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2301, c_20])).
% 5.55/2.02  tff(c_2431, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2344, c_2351])).
% 5.55/2.02  tff(c_16, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.55/2.02  tff(c_12, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.55/2.02  tff(c_2015, plain, (![A_157]: (k5_relat_1(A_157, k2_funct_1(A_157))=k6_partfun1(k1_relat_1(A_157)) | ~v2_funct_1(A_157) | ~v1_funct_1(A_157) | ~v1_relat_1(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 5.55/2.02  tff(c_2024, plain, (![A_6]: (k6_partfun1(k1_relat_1(k2_funct_1(A_6)))=k5_relat_1(k2_funct_1(A_6), A_6) | ~v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2015])).
% 5.55/2.02  tff(c_2435, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2431, c_2024])).
% 5.55/2.02  tff(c_2439, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1936, c_56, c_2041, c_2352, c_2160, c_2350, c_2435])).
% 5.55/2.02  tff(c_32, plain, (![A_21, B_22]: (m1_subset_1(k2_funct_2(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_2357, plain, (![A_207, F_203, B_205, C_202, E_204, D_206]: (k1_partfun1(A_207, B_205, C_202, D_206, E_204, F_203)=k5_relat_1(E_204, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_202, D_206))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))) | ~v1_funct_1(E_204))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.55/2.02  tff(c_2365, plain, (![A_207, B_205, E_204]: (k1_partfun1(A_207, B_205, '#skF_2', '#skF_2', E_204, '#skF_3')=k5_relat_1(E_204, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))) | ~v1_funct_1(E_204))), inference(resolution, [status(thm)], [c_50, c_2357])).
% 5.55/2.02  tff(c_2400, plain, (![A_208, B_209, E_210]: (k1_partfun1(A_208, B_209, '#skF_2', '#skF_2', E_210, '#skF_3')=k5_relat_1(E_210, '#skF_3') | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~v1_funct_1(E_210))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2365])).
% 5.55/2.02  tff(c_3172, plain, (![A_224, B_225]: (k1_partfun1(A_224, A_224, '#skF_2', '#skF_2', k2_funct_2(A_224, B_225), '#skF_3')=k5_relat_1(k2_funct_2(A_224, B_225), '#skF_3') | ~v1_funct_1(k2_funct_2(A_224, B_225)) | ~m1_subset_1(B_225, k1_zfmisc_1(k2_zfmisc_1(A_224, A_224))) | ~v3_funct_2(B_225, A_224, A_224) | ~v1_funct_2(B_225, A_224, A_224) | ~v1_funct_1(B_225))), inference(resolution, [status(thm)], [c_32, c_2400])).
% 5.55/2.02  tff(c_3184, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3172])).
% 5.55/2.02  tff(c_3199, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2160, c_2158, c_2439, c_2158, c_2158, c_3184])).
% 5.55/2.02  tff(c_211, plain, (![A_63, B_64, C_65, D_66]: (r2_relset_1(A_63, B_64, C_65, C_65) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.55/2.02  tff(c_221, plain, (![A_67, C_68]: (r2_relset_1(A_67, A_67, C_68, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, A_67))))), inference(resolution, [status(thm)], [c_57, c_211])).
% 5.55/2.02  tff(c_229, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_57, c_221])).
% 5.55/2.02  tff(c_75, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.55/2.02  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_75])).
% 5.55/2.02  tff(c_178, plain, (![C_56, A_57, B_58]: (v2_funct_1(C_56) | ~v3_funct_2(C_56, A_57, B_58) | ~v1_funct_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.55/2.02  tff(c_184, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_178])).
% 5.55/2.02  tff(c_192, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_184])).
% 5.55/2.02  tff(c_295, plain, (![A_84, B_85]: (k2_funct_2(A_84, B_85)=k2_funct_1(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_zfmisc_1(A_84, A_84))) | ~v3_funct_2(B_85, A_84, A_84) | ~v1_funct_2(B_85, A_84, A_84) | ~v1_funct_1(B_85))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.55/2.02  tff(c_301, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_295])).
% 5.55/2.02  tff(c_309, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_301])).
% 5.55/2.02  tff(c_349, plain, (![A_97, B_98]: (m1_subset_1(k2_funct_2(A_97, B_98), k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_379, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_309, c_349])).
% 5.55/2.02  tff(c_391, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_379])).
% 5.55/2.02  tff(c_442, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_18])).
% 5.55/2.02  tff(c_274, plain, (![A_76, B_77]: (v1_funct_1(k2_funct_2(A_76, B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))) | ~v3_funct_2(B_77, A_76, A_76) | ~v1_funct_2(B_77, A_76, A_76) | ~v1_funct_1(B_77))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_280, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_274])).
% 5.55/2.02  tff(c_288, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_280])).
% 5.55/2.02  tff(c_311, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_288])).
% 5.55/2.02  tff(c_317, plain, (![A_86, B_87]: (v3_funct_2(k2_funct_2(A_86, B_87), A_86, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(k2_zfmisc_1(A_86, A_86))) | ~v3_funct_2(B_87, A_86, A_86) | ~v1_funct_2(B_87, A_86, A_86) | ~v1_funct_1(B_87))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_321, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_317])).
% 5.55/2.02  tff(c_328, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_309, c_321])).
% 5.55/2.02  tff(c_412, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_28])).
% 5.55/2.02  tff(c_440, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_328, c_412])).
% 5.55/2.02  tff(c_10, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.55/2.02  tff(c_166, plain, (![A_55]: (k5_relat_1(k2_funct_1(A_55), A_55)=k6_partfun1(k2_relat_1(A_55)) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.55/2.02  tff(c_175, plain, (![A_6]: (k6_partfun1(k2_relat_1(k2_funct_1(A_6)))=k5_relat_1(A_6, k2_funct_1(A_6)) | ~v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_166])).
% 5.55/2.02  tff(c_334, plain, (![A_93, B_94]: (v1_funct_2(k2_funct_2(A_93, B_94), A_93, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_338, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_334])).
% 5.55/2.02  tff(c_345, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_309, c_338])).
% 5.55/2.02  tff(c_42, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.55/2.02  tff(c_398, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_42])).
% 5.55/2.02  tff(c_427, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_345, c_328, c_398])).
% 5.55/2.02  tff(c_526, plain, (![A_108, B_109]: (v1_relat_1(k2_funct_2(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(resolution, [status(thm)], [c_349, c_18])).
% 5.55/2.02  tff(c_529, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_526])).
% 5.55/2.02  tff(c_545, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_345, c_328, c_427, c_529])).
% 5.55/2.02  tff(c_38, plain, (![A_21, B_22]: (v1_funct_1(k2_funct_2(A_21, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_401, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_38])).
% 5.55/2.02  tff(c_430, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_345, c_328, c_401])).
% 5.55/2.02  tff(c_469, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_427, c_430])).
% 5.55/2.02  tff(c_34, plain, (![A_21, B_22]: (v3_funct_2(k2_funct_2(A_21, B_22), A_21, A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_395, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_34])).
% 5.55/2.02  tff(c_424, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_345, c_328, c_395])).
% 5.55/2.02  tff(c_468, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_424])).
% 5.55/2.02  tff(c_473, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_427, c_32])).
% 5.55/2.02  tff(c_477, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_345, c_328, c_391, c_473])).
% 5.55/2.02  tff(c_585, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_28])).
% 5.55/2.02  tff(c_625, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_468, c_585])).
% 5.55/2.02  tff(c_36, plain, (![A_21, B_22]: (v1_funct_2(k2_funct_2(A_21, B_22), A_21, A_21) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.55/2.02  tff(c_393, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_391, c_36])).
% 5.55/2.02  tff(c_421, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_345, c_328, c_393])).
% 5.55/2.02  tff(c_515, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_421])).
% 5.55/2.02  tff(c_577, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_46])).
% 5.55/2.02  tff(c_618, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_469, c_515, c_577])).
% 5.55/2.02  tff(c_626, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_20])).
% 5.55/2.02  tff(c_1165, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_618, c_626])).
% 5.55/2.02  tff(c_571, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_42])).
% 5.55/2.02  tff(c_612, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_515, c_468, c_571])).
% 5.55/2.02  tff(c_840, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_612])).
% 5.55/2.02  tff(c_846, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_56, c_192, c_309, c_840])).
% 5.55/2.02  tff(c_1021, plain, (![A_118]: (k6_partfun1(k2_relat_1(k2_funct_1(A_118)))=k5_relat_1(A_118, k2_funct_1(A_118)) | ~v2_funct_1(k2_funct_1(A_118)) | ~v1_funct_1(k2_funct_1(A_118)) | ~v1_relat_1(k2_funct_1(A_118)) | ~v2_funct_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_16, c_166])).
% 5.55/2.02  tff(c_1083, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_846, c_1021])).
% 5.55/2.02  tff(c_1099, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_469, c_625, c_442, c_846, c_311, c_846, c_440, c_846, c_846, c_1083])).
% 5.55/2.02  tff(c_154, plain, (![A_54]: (k5_relat_1(A_54, k2_funct_1(A_54))=k6_partfun1(k1_relat_1(A_54)) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 5.55/2.02  tff(c_163, plain, (![A_6]: (k6_partfun1(k1_relat_1(k2_funct_1(A_6)))=k5_relat_1(k2_funct_1(A_6), A_6) | ~v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_16, c_154])).
% 5.55/2.02  tff(c_1183, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1099, c_163])).
% 5.55/2.02  tff(c_1199, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_311, c_440, c_545, c_469, c_625, c_1165, c_1183])).
% 5.55/2.02  tff(c_1257, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_1199])).
% 5.55/2.02  tff(c_1276, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_56, c_192, c_442, c_311, c_440, c_1257])).
% 5.55/2.02  tff(c_443, plain, (![C_99, D_103, B_102, A_104, F_100, E_101]: (k1_partfun1(A_104, B_102, C_99, D_103, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_103))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.55/2.02  tff(c_445, plain, (![A_104, B_102, E_101]: (k1_partfun1(A_104, B_102, '#skF_2', '#skF_2', E_101, k2_funct_1('#skF_3'))=k5_relat_1(E_101, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(resolution, [status(thm)], [c_391, c_443])).
% 5.55/2.02  tff(c_1865, plain, (![A_138, B_139, E_140]: (k1_partfun1(A_138, B_139, '#skF_2', '#skF_2', E_140, k2_funct_1('#skF_3'))=k5_relat_1(E_140, k2_funct_1('#skF_3')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_445])).
% 5.55/2.02  tff(c_1895, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1865])).
% 5.55/2.02  tff(c_1915, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1276, c_1895])).
% 5.55/2.02  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.55/2.02  tff(c_73, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.55/2.02  tff(c_312, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_73])).
% 5.55/2.02  tff(c_1917, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_312])).
% 5.55/2.02  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_1917])).
% 5.55/2.02  tff(c_1921, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 5.55/2.02  tff(c_2162, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_1921])).
% 5.55/2.02  tff(c_3231, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3199, c_2162])).
% 5.55/2.02  tff(c_3234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2106, c_3231])).
% 5.55/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.02  
% 5.55/2.02  Inference rules
% 5.55/2.02  ----------------------
% 5.55/2.02  #Ref     : 0
% 5.55/2.02  #Sup     : 770
% 5.55/2.02  #Fact    : 0
% 5.55/2.02  #Define  : 0
% 5.55/2.02  #Split   : 3
% 5.55/2.02  #Chain   : 0
% 5.55/2.02  #Close   : 0
% 5.55/2.02  
% 5.55/2.02  Ordering : KBO
% 5.55/2.02  
% 5.55/2.02  Simplification rules
% 5.55/2.02  ----------------------
% 5.55/2.02  #Subsume      : 94
% 5.55/2.02  #Demod        : 1364
% 5.55/2.02  #Tautology    : 325
% 5.55/2.02  #SimpNegUnit  : 0
% 5.55/2.02  #BackRed      : 31
% 5.55/2.02  
% 5.55/2.02  #Partial instantiations: 0
% 5.55/2.02  #Strategies tried      : 1
% 5.55/2.02  
% 5.55/2.02  Timing (in seconds)
% 5.55/2.02  ----------------------
% 5.55/2.02  Preprocessing        : 0.35
% 5.55/2.02  Parsing              : 0.20
% 5.55/2.03  CNF conversion       : 0.02
% 5.55/2.03  Main loop            : 0.88
% 5.55/2.03  Inferencing          : 0.30
% 5.55/2.03  Reduction            : 0.33
% 5.55/2.03  Demodulation         : 0.25
% 5.55/2.03  BG Simplification    : 0.04
% 5.55/2.03  Subsumption          : 0.14
% 5.55/2.03  Abstraction          : 0.04
% 5.55/2.03  MUC search           : 0.00
% 5.55/2.03  Cooper               : 0.00
% 5.55/2.03  Total                : 1.29
% 5.55/2.03  Index Insertion      : 0.00
% 5.55/2.03  Index Deletion       : 0.00
% 5.55/2.03  Index Matching       : 0.00
% 5.55/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
