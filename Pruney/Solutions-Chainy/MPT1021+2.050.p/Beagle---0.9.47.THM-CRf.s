%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:07 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  166 (3196 expanded)
%              Number of leaves         :   40 (1299 expanded)
%              Depth                    :   21
%              Number of atoms          :  386 (11594 expanded)
%              Number of equality atoms :   55 ( 601 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_133,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_40,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2077,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( r2_relset_1(A_169,B_170,C_171,C_171)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2087,plain,(
    ! [A_173,C_174] :
      ( r2_relset_1(A_173,A_173,C_174,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,A_173))) ) ),
    inference(resolution,[status(thm)],[c_40,c_2077])).

tff(c_2095,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_40,c_2087])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2131,plain,(
    ! [A_184,B_185] :
      ( k2_funct_2(A_184,B_185) = k2_funct_1(B_185)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_zfmisc_1(A_184,A_184)))
      | ~ v3_funct_2(B_185,A_184,A_184)
      | ~ v1_funct_2(B_185,A_184,A_184)
      | ~ v1_funct_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2137,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2131])).

tff(c_2145,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2137])).

tff(c_2112,plain,(
    ! [A_179,B_180] :
      ( v1_funct_1(k2_funct_2(A_179,B_180))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_zfmisc_1(A_179,A_179)))
      | ~ v3_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2118,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2112])).

tff(c_2126,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2118])).

tff(c_2147,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_2126])).

tff(c_1913,plain,(
    ! [C_143,A_144,B_145] :
      ( v1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1925,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1913])).

tff(c_2016,plain,(
    ! [C_159,A_160,B_161] :
      ( v2_funct_1(C_159)
      | ~ v3_funct_2(C_159,A_160,B_161)
      | ~ v1_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2022,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2016])).

tff(c_2030,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2022])).

tff(c_2187,plain,(
    ! [A_199,B_200] :
      ( m1_subset_1(k2_funct_2(A_199,B_200),k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ v3_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2217,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2145,c_2187])).

tff(c_2229,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2217])).

tff(c_18,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2280,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2229,c_18])).

tff(c_2170,plain,(
    ! [A_193,B_194] :
      ( v3_funct_2(k2_funct_2(A_193,B_194),A_193,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2174,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2170])).

tff(c_2181,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2145,c_2174])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( v2_funct_1(C_19)
      | ~ v3_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2250,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2229,c_26])).

tff(c_2278,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2181,c_2250])).

tff(c_2155,plain,(
    ! [A_187,B_188] :
      ( v1_funct_2(k2_funct_2(A_187,B_188),A_187,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2159,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2155])).

tff(c_2166,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2145,c_2159])).

tff(c_48,plain,(
    ! [A_32,B_33] :
      ( k1_relset_1(A_32,A_32,B_33) = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2244,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2229,c_48])).

tff(c_2272,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2166,c_2244])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2279,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2229,c_20])).

tff(c_2333,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2272,c_2279])).

tff(c_16,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2004,plain,(
    ! [A_158] :
      ( k5_relat_1(A_158,k2_funct_1(A_158)) = k6_partfun1(k1_relat_1(A_158))
      | ~ v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_2669,plain,(
    ! [A_214] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_214))) = k5_relat_1(k2_funct_1(A_214),A_214)
      | ~ v2_funct_1(k2_funct_1(A_214))
      | ~ v1_funct_1(k2_funct_1(A_214))
      | ~ v1_relat_1(k2_funct_1(A_214))
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2004])).

tff(c_2729,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2333,c_2669])).

tff(c_2743,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1925,c_58,c_2030,c_2280,c_2147,c_2278,c_2729])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2300,plain,(
    ! [D_205,B_204,A_206,F_202,C_201,E_203] :
      ( k1_partfun1(A_206,B_204,C_201,D_205,E_203,F_202) = k5_relat_1(E_203,F_202)
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_201,D_205)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_204)))
      | ~ v1_funct_1(E_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2308,plain,(
    ! [A_206,B_204,E_203] :
      ( k1_partfun1(A_206,B_204,'#skF_2','#skF_2',E_203,'#skF_3') = k5_relat_1(E_203,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_204)))
      | ~ v1_funct_1(E_203) ) ),
    inference(resolution,[status(thm)],[c_52,c_2300])).

tff(c_2338,plain,(
    ! [A_207,B_208,E_209] :
      ( k1_partfun1(A_207,B_208,'#skF_2','#skF_2',E_209,'#skF_3') = k5_relat_1(E_209,'#skF_3')
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_1(E_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2308])).

tff(c_2983,plain,(
    ! [A_218,B_219] :
      ( k1_partfun1(A_218,A_218,'#skF_2','#skF_2',k2_funct_2(A_218,B_219),'#skF_3') = k5_relat_1(k2_funct_2(A_218,B_219),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_218,B_219))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k2_zfmisc_1(A_218,A_218)))
      | ~ v3_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_1(B_219) ) ),
    inference(resolution,[status(thm)],[c_30,c_2338])).

tff(c_2993,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2983])).

tff(c_3007,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2147,c_2145,c_2743,c_2145,c_2145,c_2993])).

tff(c_214,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_relset_1(A_65,B_66,C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_224,plain,(
    ! [A_69,C_70] :
      ( r2_relset_1(A_69,A_69,C_70,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,A_69))) ) ),
    inference(resolution,[status(thm)],[c_40,c_214])).

tff(c_232,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_40,c_224])).

tff(c_77,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_180,plain,(
    ! [C_57,A_58,B_59] :
      ( v2_funct_1(C_57)
      | ~ v3_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_186,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_180])).

tff(c_194,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_186])).

tff(c_296,plain,(
    ! [A_83,B_84] :
      ( k2_funct_2(A_83,B_84) = k2_funct_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_302,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_296])).

tff(c_310,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_302])).

tff(c_263,plain,(
    ! [A_74,B_75] :
      ( v1_funct_1(k2_funct_2(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_zfmisc_1(A_74,A_74)))
      | ~ v3_funct_2(B_75,A_74,A_74)
      | ~ v1_funct_2(B_75,A_74,A_74)
      | ~ v1_funct_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_269,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_263])).

tff(c_277,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_269])).

tff(c_312,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_277])).

tff(c_335,plain,(
    ! [A_93,B_94] :
      ( v1_funct_2(k2_funct_2(A_93,B_94),A_93,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_339,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_335])).

tff(c_346,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_310,c_339])).

tff(c_318,plain,(
    ! [A_85,B_86] :
      ( v3_funct_2(k2_funct_2(A_85,B_86),A_85,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_322,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_318])).

tff(c_329,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_310,c_322])).

tff(c_350,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k2_funct_2(A_97,B_98),k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_380,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_350])).

tff(c_392,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_380])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_399,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_392,c_44])).

tff(c_428,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_346,c_329,c_399])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k2_funct_2(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_404,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_392,c_36])).

tff(c_432,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_346,c_329,c_404])).

tff(c_469,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_432])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( v1_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_394,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_392,c_34])).

tff(c_422,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_346,c_329,c_394])).

tff(c_510,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_422])).

tff(c_473,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_30])).

tff(c_477,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_346,c_329,c_392,c_473])).

tff(c_546,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_48])).

tff(c_583,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_510,c_546])).

tff(c_590,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_20])).

tff(c_811,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_590])).

tff(c_591,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_18])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( v3_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_396,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_392,c_32])).

tff(c_425,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_346,c_329,c_396])).

tff(c_516,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_425])).

tff(c_552,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_26])).

tff(c_589,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_516,c_552])).

tff(c_538,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_477,c_44])).

tff(c_576,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_510,c_516,c_538])).

tff(c_707,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_576])).

tff(c_713,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_58,c_194,c_310,c_707])).

tff(c_59,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_partfun1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_745,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_59])).

tff(c_772,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_469,c_589,c_745])).

tff(c_821,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_772])).

tff(c_832,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_821])).

tff(c_840,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_58,c_194,c_832])).

tff(c_444,plain,(
    ! [C_99,D_103,B_102,A_104,F_100,E_101] :
      ( k1_partfun1(A_104,B_102,C_99,D_103,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_99,D_103)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_446,plain,(
    ! [A_104,B_102,E_101] :
      ( k1_partfun1(A_104,B_102,'#skF_2','#skF_2',E_101,k2_funct_1('#skF_3')) = k5_relat_1(E_101,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(resolution,[status(thm)],[c_392,c_444])).

tff(c_1853,plain,(
    ! [A_138,B_139,E_140] :
      ( k1_partfun1(A_138,B_139,'#skF_2','#skF_2',E_140,k2_funct_1('#skF_3')) = k5_relat_1(E_140,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_446])).

tff(c_1883,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1853])).

tff(c_1903,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_840,c_1883])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_313,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_74])).

tff(c_1905,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1903,c_313])).

tff(c_1908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_1905])).

tff(c_1909,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2149,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_1909])).

tff(c_3063,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3007,c_2149])).

tff(c_3066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2095,c_3063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:11:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.95  
% 5.17/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.96  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.17/1.96  
% 5.17/1.96  %Foreground sorts:
% 5.17/1.96  
% 5.17/1.96  
% 5.17/1.96  %Background operators:
% 5.17/1.96  
% 5.17/1.96  
% 5.17/1.96  %Foreground operators:
% 5.17/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.17/1.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.17/1.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.17/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/1.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.17/1.96  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.17/1.96  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.17/1.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.17/1.96  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.17/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/1.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.17/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.17/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.17/1.96  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.17/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.17/1.96  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.17/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.17/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.17/1.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.17/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.17/1.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.17/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/1.96  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.17/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.17/1.96  
% 5.44/1.98  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.44/1.98  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.44/1.98  tff(f_154, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.44/1.98  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.44/1.98  tff(f_107, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.44/1.98  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.44/1.98  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.44/1.98  tff(f_141, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.44/1.98  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.44/1.98  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.44/1.98  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.44/1.98  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.44/1.98  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.44/1.98  tff(c_40, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.44/1.98  tff(c_2077, plain, (![A_169, B_170, C_171, D_172]: (r2_relset_1(A_169, B_170, C_171, C_171) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.44/1.98  tff(c_2087, plain, (![A_173, C_174]: (r2_relset_1(A_173, A_173, C_174, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, A_173))))), inference(resolution, [status(thm)], [c_40, c_2077])).
% 5.44/1.98  tff(c_2095, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_40, c_2087])).
% 5.44/1.98  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.44/1.98  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.44/1.98  tff(c_54, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.44/1.98  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.44/1.98  tff(c_2131, plain, (![A_184, B_185]: (k2_funct_2(A_184, B_185)=k2_funct_1(B_185) | ~m1_subset_1(B_185, k1_zfmisc_1(k2_zfmisc_1(A_184, A_184))) | ~v3_funct_2(B_185, A_184, A_184) | ~v1_funct_2(B_185, A_184, A_184) | ~v1_funct_1(B_185))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/1.98  tff(c_2137, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2131])).
% 5.44/1.98  tff(c_2145, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2137])).
% 5.44/1.98  tff(c_2112, plain, (![A_179, B_180]: (v1_funct_1(k2_funct_2(A_179, B_180)) | ~m1_subset_1(B_180, k1_zfmisc_1(k2_zfmisc_1(A_179, A_179))) | ~v3_funct_2(B_180, A_179, A_179) | ~v1_funct_2(B_180, A_179, A_179) | ~v1_funct_1(B_180))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_2118, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2112])).
% 5.44/1.98  tff(c_2126, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2118])).
% 5.44/1.98  tff(c_2147, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_2126])).
% 5.44/1.98  tff(c_1913, plain, (![C_143, A_144, B_145]: (v1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.44/1.98  tff(c_1925, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1913])).
% 5.44/1.98  tff(c_2016, plain, (![C_159, A_160, B_161]: (v2_funct_1(C_159) | ~v3_funct_2(C_159, A_160, B_161) | ~v1_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.44/1.98  tff(c_2022, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2016])).
% 5.44/1.98  tff(c_2030, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2022])).
% 5.44/1.98  tff(c_2187, plain, (![A_199, B_200]: (m1_subset_1(k2_funct_2(A_199, B_200), k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~v3_funct_2(B_200, A_199, A_199) | ~v1_funct_2(B_200, A_199, A_199) | ~v1_funct_1(B_200))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_2217, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2145, c_2187])).
% 5.44/1.98  tff(c_2229, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2217])).
% 5.44/1.98  tff(c_18, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.44/1.98  tff(c_2280, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2229, c_18])).
% 5.44/1.98  tff(c_2170, plain, (![A_193, B_194]: (v3_funct_2(k2_funct_2(A_193, B_194), A_193, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_2174, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2170])).
% 5.44/1.98  tff(c_2181, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2145, c_2174])).
% 5.44/1.98  tff(c_26, plain, (![C_19, A_17, B_18]: (v2_funct_1(C_19) | ~v3_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.44/1.98  tff(c_2250, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2229, c_26])).
% 5.44/1.98  tff(c_2278, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2181, c_2250])).
% 5.44/1.98  tff(c_2155, plain, (![A_187, B_188]: (v1_funct_2(k2_funct_2(A_187, B_188), A_187, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_188, A_187, A_187) | ~v1_funct_2(B_188, A_187, A_187) | ~v1_funct_1(B_188))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_2159, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2155])).
% 5.44/1.98  tff(c_2166, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2145, c_2159])).
% 5.44/1.98  tff(c_48, plain, (![A_32, B_33]: (k1_relset_1(A_32, A_32, B_33)=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.44/1.98  tff(c_2244, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2229, c_48])).
% 5.44/1.98  tff(c_2272, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2166, c_2244])).
% 5.44/1.98  tff(c_20, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.44/1.98  tff(c_2279, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2229, c_20])).
% 5.44/1.98  tff(c_2333, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2272, c_2279])).
% 5.44/1.98  tff(c_16, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.44/1.98  tff(c_46, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.44/1.98  tff(c_12, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.44/1.98  tff(c_2004, plain, (![A_158]: (k5_relat_1(A_158, k2_funct_1(A_158))=k6_partfun1(k1_relat_1(A_158)) | ~v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.44/1.98  tff(c_2669, plain, (![A_214]: (k6_partfun1(k1_relat_1(k2_funct_1(A_214)))=k5_relat_1(k2_funct_1(A_214), A_214) | ~v2_funct_1(k2_funct_1(A_214)) | ~v1_funct_1(k2_funct_1(A_214)) | ~v1_relat_1(k2_funct_1(A_214)) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2004])).
% 5.44/1.98  tff(c_2729, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2333, c_2669])).
% 5.44/1.98  tff(c_2743, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1925, c_58, c_2030, c_2280, c_2147, c_2278, c_2729])).
% 5.44/1.98  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_2300, plain, (![D_205, B_204, A_206, F_202, C_201, E_203]: (k1_partfun1(A_206, B_204, C_201, D_205, E_203, F_202)=k5_relat_1(E_203, F_202) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_201, D_205))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_204))) | ~v1_funct_1(E_203))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.44/1.98  tff(c_2308, plain, (![A_206, B_204, E_203]: (k1_partfun1(A_206, B_204, '#skF_2', '#skF_2', E_203, '#skF_3')=k5_relat_1(E_203, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_204))) | ~v1_funct_1(E_203))), inference(resolution, [status(thm)], [c_52, c_2300])).
% 5.44/1.98  tff(c_2338, plain, (![A_207, B_208, E_209]: (k1_partfun1(A_207, B_208, '#skF_2', '#skF_2', E_209, '#skF_3')=k5_relat_1(E_209, '#skF_3') | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_1(E_209))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2308])).
% 5.44/1.98  tff(c_2983, plain, (![A_218, B_219]: (k1_partfun1(A_218, A_218, '#skF_2', '#skF_2', k2_funct_2(A_218, B_219), '#skF_3')=k5_relat_1(k2_funct_2(A_218, B_219), '#skF_3') | ~v1_funct_1(k2_funct_2(A_218, B_219)) | ~m1_subset_1(B_219, k1_zfmisc_1(k2_zfmisc_1(A_218, A_218))) | ~v3_funct_2(B_219, A_218, A_218) | ~v1_funct_2(B_219, A_218, A_218) | ~v1_funct_1(B_219))), inference(resolution, [status(thm)], [c_30, c_2338])).
% 5.44/1.98  tff(c_2993, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2983])).
% 5.44/1.98  tff(c_3007, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2147, c_2145, c_2743, c_2145, c_2145, c_2993])).
% 5.44/1.98  tff(c_214, plain, (![A_65, B_66, C_67, D_68]: (r2_relset_1(A_65, B_66, C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.44/1.98  tff(c_224, plain, (![A_69, C_70]: (r2_relset_1(A_69, A_69, C_70, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))))), inference(resolution, [status(thm)], [c_40, c_214])).
% 5.44/1.98  tff(c_232, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_40, c_224])).
% 5.44/1.98  tff(c_77, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.44/1.98  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_77])).
% 5.44/1.98  tff(c_180, plain, (![C_57, A_58, B_59]: (v2_funct_1(C_57) | ~v3_funct_2(C_57, A_58, B_59) | ~v1_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.44/1.98  tff(c_186, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_180])).
% 5.44/1.98  tff(c_194, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_186])).
% 5.44/1.98  tff(c_296, plain, (![A_83, B_84]: (k2_funct_2(A_83, B_84)=k2_funct_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/1.98  tff(c_302, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_296])).
% 5.44/1.98  tff(c_310, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_302])).
% 5.44/1.98  tff(c_263, plain, (![A_74, B_75]: (v1_funct_1(k2_funct_2(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_zfmisc_1(A_74, A_74))) | ~v3_funct_2(B_75, A_74, A_74) | ~v1_funct_2(B_75, A_74, A_74) | ~v1_funct_1(B_75))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_269, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_263])).
% 5.44/1.98  tff(c_277, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_269])).
% 5.44/1.98  tff(c_312, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_277])).
% 5.44/1.98  tff(c_335, plain, (![A_93, B_94]: (v1_funct_2(k2_funct_2(A_93, B_94), A_93, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_339, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_335])).
% 5.44/1.98  tff(c_346, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_310, c_339])).
% 5.44/1.98  tff(c_318, plain, (![A_85, B_86]: (v3_funct_2(k2_funct_2(A_85, B_86), A_85, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_322, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_318])).
% 5.44/1.98  tff(c_329, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_310, c_322])).
% 5.44/1.98  tff(c_350, plain, (![A_97, B_98]: (m1_subset_1(k2_funct_2(A_97, B_98), k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_380, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_310, c_350])).
% 5.44/1.98  tff(c_392, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_380])).
% 5.44/1.98  tff(c_44, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/1.98  tff(c_399, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_392, c_44])).
% 5.44/1.98  tff(c_428, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_346, c_329, c_399])).
% 5.44/1.98  tff(c_36, plain, (![A_20, B_21]: (v1_funct_1(k2_funct_2(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_404, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_392, c_36])).
% 5.44/1.98  tff(c_432, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_346, c_329, c_404])).
% 5.44/1.98  tff(c_469, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_428, c_432])).
% 5.44/1.98  tff(c_34, plain, (![A_20, B_21]: (v1_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_394, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_392, c_34])).
% 5.44/1.98  tff(c_422, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_346, c_329, c_394])).
% 5.44/1.98  tff(c_510, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_422])).
% 5.44/1.98  tff(c_473, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_428, c_30])).
% 5.44/1.98  tff(c_477, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_346, c_329, c_392, c_473])).
% 5.44/1.98  tff(c_546, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_48])).
% 5.44/1.98  tff(c_583, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_469, c_510, c_546])).
% 5.44/1.98  tff(c_590, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_20])).
% 5.44/1.98  tff(c_811, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_583, c_590])).
% 5.44/1.98  tff(c_591, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_18])).
% 5.44/1.98  tff(c_32, plain, (![A_20, B_21]: (v3_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.44/1.98  tff(c_396, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_392, c_32])).
% 5.44/1.98  tff(c_425, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_346, c_329, c_396])).
% 5.44/1.98  tff(c_516, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_425])).
% 5.44/1.98  tff(c_552, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_26])).
% 5.44/1.98  tff(c_589, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_516, c_552])).
% 5.44/1.98  tff(c_538, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_477, c_44])).
% 5.44/1.98  tff(c_576, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_510, c_516, c_538])).
% 5.44/1.98  tff(c_707, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_576])).
% 5.44/1.98  tff(c_713, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_58, c_194, c_310, c_707])).
% 5.44/1.98  tff(c_59, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_partfun1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.44/1.98  tff(c_745, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_713, c_59])).
% 5.44/1.98  tff(c_772, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_591, c_469, c_589, c_745])).
% 5.44/1.98  tff(c_821, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_772])).
% 5.44/1.98  tff(c_832, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_821])).
% 5.44/1.98  tff(c_840, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_58, c_194, c_832])).
% 5.44/1.98  tff(c_444, plain, (![C_99, D_103, B_102, A_104, F_100, E_101]: (k1_partfun1(A_104, B_102, C_99, D_103, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_103))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.44/1.98  tff(c_446, plain, (![A_104, B_102, E_101]: (k1_partfun1(A_104, B_102, '#skF_2', '#skF_2', E_101, k2_funct_1('#skF_3'))=k5_relat_1(E_101, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(resolution, [status(thm)], [c_392, c_444])).
% 5.44/1.98  tff(c_1853, plain, (![A_138, B_139, E_140]: (k1_partfun1(A_138, B_139, '#skF_2', '#skF_2', E_140, k2_funct_1('#skF_3'))=k5_relat_1(E_140, k2_funct_1('#skF_3')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_446])).
% 5.44/1.98  tff(c_1883, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1853])).
% 5.44/1.98  tff(c_1903, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_840, c_1883])).
% 5.44/1.98  tff(c_50, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.44/1.98  tff(c_74, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.44/1.98  tff(c_313, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_74])).
% 5.44/1.98  tff(c_1905, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1903, c_313])).
% 5.44/1.98  tff(c_1908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_1905])).
% 5.44/1.98  tff(c_1909, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 5.44/1.98  tff(c_2149, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_1909])).
% 5.44/1.98  tff(c_3063, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3007, c_2149])).
% 5.44/1.98  tff(c_3066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2095, c_3063])).
% 5.44/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/1.98  
% 5.44/1.98  Inference rules
% 5.44/1.98  ----------------------
% 5.44/1.98  #Ref     : 0
% 5.44/1.98  #Sup     : 729
% 5.44/1.98  #Fact    : 0
% 5.44/1.98  #Define  : 0
% 5.44/1.98  #Split   : 2
% 5.44/1.98  #Chain   : 0
% 5.44/1.98  #Close   : 0
% 5.44/1.98  
% 5.44/1.98  Ordering : KBO
% 5.44/1.98  
% 5.44/1.98  Simplification rules
% 5.44/1.98  ----------------------
% 5.44/1.98  #Subsume      : 76
% 5.44/1.98  #Demod        : 1231
% 5.44/1.98  #Tautology    : 299
% 5.44/1.98  #SimpNegUnit  : 0
% 5.44/1.98  #BackRed      : 26
% 5.44/1.98  
% 5.44/1.98  #Partial instantiations: 0
% 5.44/1.98  #Strategies tried      : 1
% 5.44/1.98  
% 5.44/1.98  Timing (in seconds)
% 5.44/1.98  ----------------------
% 5.44/1.99  Preprocessing        : 0.34
% 5.44/1.99  Parsing              : 0.18
% 5.44/1.99  CNF conversion       : 0.02
% 5.44/1.99  Main loop            : 0.88
% 5.44/1.99  Inferencing          : 0.29
% 5.44/1.99  Reduction            : 0.35
% 5.44/1.99  Demodulation         : 0.26
% 5.44/1.99  BG Simplification    : 0.04
% 5.44/1.99  Subsumption          : 0.14
% 5.44/1.99  Abstraction          : 0.04
% 5.44/1.99  MUC search           : 0.00
% 5.44/1.99  Cooper               : 0.00
% 5.44/1.99  Total                : 1.27
% 5.44/1.99  Index Insertion      : 0.00
% 5.44/1.99  Index Deletion       : 0.00
% 5.44/1.99  Index Matching       : 0.00
% 5.44/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
