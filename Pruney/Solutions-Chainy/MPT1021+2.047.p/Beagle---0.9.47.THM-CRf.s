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
% DateTime   : Thu Dec  3 10:16:07 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.62s
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

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_158,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_111,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_44,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2081,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( r2_relset_1(A_169,B_170,C_171,C_171)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2091,plain,(
    ! [A_173,C_174] :
      ( r2_relset_1(A_173,A_173,C_174,C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,A_173))) ) ),
    inference(resolution,[status(thm)],[c_44,c_2081])).

tff(c_2099,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_44,c_2091])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2135,plain,(
    ! [A_184,B_185] :
      ( k2_funct_2(A_184,B_185) = k2_funct_1(B_185)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_zfmisc_1(A_184,A_184)))
      | ~ v3_funct_2(B_185,A_184,A_184)
      | ~ v1_funct_2(B_185,A_184,A_184)
      | ~ v1_funct_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2141,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2135])).

tff(c_2149,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2141])).

tff(c_2116,plain,(
    ! [A_179,B_180] :
      ( v1_funct_1(k2_funct_2(A_179,B_180))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_zfmisc_1(A_179,A_179)))
      | ~ v3_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_2(B_180,A_179,A_179)
      | ~ v1_funct_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2122,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2116])).

tff(c_2130,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2122])).

tff(c_2151,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_2130])).

tff(c_1917,plain,(
    ! [C_143,A_144,B_145] :
      ( v1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1929,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1917])).

tff(c_2020,plain,(
    ! [C_159,A_160,B_161] :
      ( v2_funct_1(C_159)
      | ~ v3_funct_2(C_159,A_160,B_161)
      | ~ v1_funct_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2026,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2020])).

tff(c_2034,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2026])).

tff(c_2191,plain,(
    ! [A_199,B_200] :
      ( m1_subset_1(k2_funct_2(A_199,B_200),k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ v3_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2221,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2149,c_2191])).

tff(c_2233,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_2221])).

tff(c_22,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2284,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2233,c_22])).

tff(c_2159,plain,(
    ! [A_187,B_188] :
      ( v3_funct_2(k2_funct_2(A_187,B_188),A_187,A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_2(B_188,A_187,A_187)
      | ~ v1_funct_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2163,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2159])).

tff(c_2170,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2149,c_2163])).

tff(c_30,plain,(
    ! [C_19,A_17,B_18] :
      ( v2_funct_1(C_19)
      | ~ v3_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2254,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2233,c_30])).

tff(c_2282,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2151,c_2170,c_2254])).

tff(c_2174,plain,(
    ! [A_193,B_194] :
      ( v1_funct_2(k2_funct_2(A_193,B_194),A_193,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2178,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2174])).

tff(c_2185,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2149,c_2178])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( k1_relset_1(A_32,A_32,B_33) = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2248,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2233,c_52])).

tff(c_2276,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2151,c_2185,c_2248])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2283,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2233,c_24])).

tff(c_2337,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2276,c_2283])).

tff(c_20,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_18,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_relat_1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2008,plain,(
    ! [A_158] :
      ( k5_relat_1(A_158,k2_funct_1(A_158)) = k6_partfun1(k1_relat_1(A_158))
      | ~ v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_2673,plain,(
    ! [A_214] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_214))) = k5_relat_1(k2_funct_1(A_214),A_214)
      | ~ v2_funct_1(k2_funct_1(A_214))
      | ~ v1_funct_1(k2_funct_1(A_214))
      | ~ v1_relat_1(k2_funct_1(A_214))
      | ~ v2_funct_1(A_214)
      | ~ v1_funct_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2008])).

tff(c_2733,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2337,c_2673])).

tff(c_2747,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1929,c_62,c_2034,c_2284,c_2151,c_2282,c_2733])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2304,plain,(
    ! [D_205,B_204,A_206,F_202,C_201,E_203] :
      ( k1_partfun1(A_206,B_204,C_201,D_205,E_203,F_202) = k5_relat_1(E_203,F_202)
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_201,D_205)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_204)))
      | ~ v1_funct_1(E_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2312,plain,(
    ! [A_206,B_204,E_203] :
      ( k1_partfun1(A_206,B_204,'#skF_2','#skF_2',E_203,'#skF_3') = k5_relat_1(E_203,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_204)))
      | ~ v1_funct_1(E_203) ) ),
    inference(resolution,[status(thm)],[c_56,c_2304])).

tff(c_2342,plain,(
    ! [A_207,B_208,E_209] :
      ( k1_partfun1(A_207,B_208,'#skF_2','#skF_2',E_209,'#skF_3') = k5_relat_1(E_209,'#skF_3')
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_1(E_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2312])).

tff(c_2987,plain,(
    ! [A_218,B_219] :
      ( k1_partfun1(A_218,A_218,'#skF_2','#skF_2',k2_funct_2(A_218,B_219),'#skF_3') = k5_relat_1(k2_funct_2(A_218,B_219),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_218,B_219))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k2_zfmisc_1(A_218,A_218)))
      | ~ v3_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_1(B_219) ) ),
    inference(resolution,[status(thm)],[c_34,c_2342])).

tff(c_2997,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2987])).

tff(c_3011,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2151,c_2149,c_2747,c_2149,c_2149,c_2997])).

tff(c_218,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_relset_1(A_65,B_66,C_67,C_67)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_228,plain,(
    ! [A_69,C_70] :
      ( r2_relset_1(A_69,A_69,C_70,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,A_69))) ) ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_236,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_44,c_228])).

tff(c_81,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_184,plain,(
    ! [C_57,A_58,B_59] :
      ( v2_funct_1(C_57)
      | ~ v3_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_190,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_184])).

tff(c_198,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_190])).

tff(c_300,plain,(
    ! [A_83,B_84] :
      ( k2_funct_2(A_83,B_84) = k2_funct_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_306,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_300])).

tff(c_314,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_306])).

tff(c_267,plain,(
    ! [A_74,B_75] :
      ( v1_funct_1(k2_funct_2(A_74,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_zfmisc_1(A_74,A_74)))
      | ~ v3_funct_2(B_75,A_74,A_74)
      | ~ v1_funct_2(B_75,A_74,A_74)
      | ~ v1_funct_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_273,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_267])).

tff(c_281,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_273])).

tff(c_316,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_281])).

tff(c_322,plain,(
    ! [A_85,B_86] :
      ( v1_funct_2(k2_funct_2(A_85,B_86),A_85,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_326,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_322])).

tff(c_333,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_314,c_326])).

tff(c_339,plain,(
    ! [A_93,B_94] :
      ( v3_funct_2(k2_funct_2(A_93,B_94),A_93,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_343,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_339])).

tff(c_350,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_314,c_343])).

tff(c_354,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k2_funct_2(A_97,B_98),k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_384,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_354])).

tff(c_396,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_384])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_403,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_396,c_48])).

tff(c_432,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_333,c_350,c_403])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k2_funct_2(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_408,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_396,c_40])).

tff(c_436,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_333,c_350,c_408])).

tff(c_473,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_436])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( v1_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_400,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_396,c_38])).

tff(c_429,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_333,c_350,c_400])).

tff(c_520,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_429])).

tff(c_477,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_34])).

tff(c_481,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_333,c_350,c_396,c_477])).

tff(c_550,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_481,c_52])).

tff(c_587,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_520,c_550])).

tff(c_594,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_481,c_24])).

tff(c_815,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_594])).

tff(c_595,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_481,c_22])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( v3_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_398,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_396,c_36])).

tff(c_426,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_333,c_350,c_398])).

tff(c_514,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_426])).

tff(c_556,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_481,c_30])).

tff(c_593,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_514,c_556])).

tff(c_542,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_481,c_48])).

tff(c_580,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_520,c_514,c_542])).

tff(c_711,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_580])).

tff(c_717,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_198,c_314,c_711])).

tff(c_63,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_partfun1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_749,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_63])).

tff(c_776,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_473,c_593,c_749])).

tff(c_825,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_776])).

tff(c_836,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_825])).

tff(c_844,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_198,c_836])).

tff(c_448,plain,(
    ! [C_99,D_103,B_102,A_104,F_100,E_101] :
      ( k1_partfun1(A_104,B_102,C_99,D_103,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_99,D_103)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_450,plain,(
    ! [A_104,B_102,E_101] :
      ( k1_partfun1(A_104,B_102,'#skF_2','#skF_2',E_101,k2_funct_1('#skF_3')) = k5_relat_1(E_101,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(resolution,[status(thm)],[c_396,c_448])).

tff(c_1857,plain,(
    ! [A_138,B_139,E_140] :
      ( k1_partfun1(A_138,B_139,'#skF_2','#skF_2',E_140,k2_funct_1('#skF_3')) = k5_relat_1(E_140,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_450])).

tff(c_1887,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1857])).

tff(c_1907,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_844,c_1887])).

tff(c_54,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_78,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_317,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_78])).

tff(c_1909,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_317])).

tff(c_1912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_1909])).

tff(c_1913,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2153,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2149,c_1913])).

tff(c_3067,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3011,c_2153])).

tff(c_3070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_3067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:15:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.08  
% 5.52/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.08  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.52/2.08  
% 5.52/2.08  %Foreground sorts:
% 5.52/2.08  
% 5.52/2.08  
% 5.52/2.08  %Background operators:
% 5.52/2.08  
% 5.52/2.08  
% 5.52/2.08  %Foreground operators:
% 5.52/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.52/2.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.52/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.52/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.52/2.08  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.52/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.52/2.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.52/2.08  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.52/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.52/2.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.52/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.52/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.52/2.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.52/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.52/2.08  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.52/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.52/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.52/2.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.52/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.52/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.52/2.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.52/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.08  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.52/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.52/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.52/2.08  
% 5.62/2.11  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.62/2.11  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.62/2.11  tff(f_158, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.62/2.11  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.62/2.11  tff(f_111, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.62/2.11  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.62/2.11  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.62/2.11  tff(f_145, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.62/2.11  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.62/2.11  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.62/2.11  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.62/2.11  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.62/2.11  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.62/2.11  tff(c_44, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.62/2.11  tff(c_2081, plain, (![A_169, B_170, C_171, D_172]: (r2_relset_1(A_169, B_170, C_171, C_171) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.62/2.11  tff(c_2091, plain, (![A_173, C_174]: (r2_relset_1(A_173, A_173, C_174, C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, A_173))))), inference(resolution, [status(thm)], [c_44, c_2081])).
% 5.62/2.11  tff(c_2099, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_44, c_2091])).
% 5.62/2.11  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.62/2.11  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.62/2.11  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.62/2.11  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.62/2.11  tff(c_2135, plain, (![A_184, B_185]: (k2_funct_2(A_184, B_185)=k2_funct_1(B_185) | ~m1_subset_1(B_185, k1_zfmisc_1(k2_zfmisc_1(A_184, A_184))) | ~v3_funct_2(B_185, A_184, A_184) | ~v1_funct_2(B_185, A_184, A_184) | ~v1_funct_1(B_185))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.62/2.11  tff(c_2141, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2135])).
% 5.62/2.11  tff(c_2149, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2141])).
% 5.62/2.11  tff(c_2116, plain, (![A_179, B_180]: (v1_funct_1(k2_funct_2(A_179, B_180)) | ~m1_subset_1(B_180, k1_zfmisc_1(k2_zfmisc_1(A_179, A_179))) | ~v3_funct_2(B_180, A_179, A_179) | ~v1_funct_2(B_180, A_179, A_179) | ~v1_funct_1(B_180))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_2122, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2116])).
% 5.62/2.11  tff(c_2130, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2122])).
% 5.62/2.11  tff(c_2151, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2149, c_2130])).
% 5.62/2.11  tff(c_1917, plain, (![C_143, A_144, B_145]: (v1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.62/2.11  tff(c_1929, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1917])).
% 5.62/2.11  tff(c_2020, plain, (![C_159, A_160, B_161]: (v2_funct_1(C_159) | ~v3_funct_2(C_159, A_160, B_161) | ~v1_funct_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.62/2.11  tff(c_2026, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2020])).
% 5.62/2.11  tff(c_2034, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2026])).
% 5.62/2.11  tff(c_2191, plain, (![A_199, B_200]: (m1_subset_1(k2_funct_2(A_199, B_200), k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~v3_funct_2(B_200, A_199, A_199) | ~v1_funct_2(B_200, A_199, A_199) | ~v1_funct_1(B_200))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_2221, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2149, c_2191])).
% 5.62/2.11  tff(c_2233, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_2221])).
% 5.62/2.11  tff(c_22, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.62/2.11  tff(c_2284, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2233, c_22])).
% 5.62/2.11  tff(c_2159, plain, (![A_187, B_188]: (v3_funct_2(k2_funct_2(A_187, B_188), A_187, A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_188, A_187, A_187) | ~v1_funct_2(B_188, A_187, A_187) | ~v1_funct_1(B_188))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_2163, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2159])).
% 5.62/2.11  tff(c_2170, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2149, c_2163])).
% 5.62/2.11  tff(c_30, plain, (![C_19, A_17, B_18]: (v2_funct_1(C_19) | ~v3_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.62/2.11  tff(c_2254, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2233, c_30])).
% 5.62/2.11  tff(c_2282, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2151, c_2170, c_2254])).
% 5.62/2.11  tff(c_2174, plain, (![A_193, B_194]: (v1_funct_2(k2_funct_2(A_193, B_194), A_193, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_2178, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2174])).
% 5.62/2.11  tff(c_2185, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2149, c_2178])).
% 5.62/2.11  tff(c_52, plain, (![A_32, B_33]: (k1_relset_1(A_32, A_32, B_33)=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.62/2.11  tff(c_2248, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2233, c_52])).
% 5.62/2.11  tff(c_2276, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2151, c_2185, c_2248])).
% 5.62/2.11  tff(c_24, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.62/2.11  tff(c_2283, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2233, c_24])).
% 5.62/2.11  tff(c_2337, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2276, c_2283])).
% 5.62/2.11  tff(c_20, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.62/2.11  tff(c_50, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.62/2.11  tff(c_18, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_relat_1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.62/2.11  tff(c_2008, plain, (![A_158]: (k5_relat_1(A_158, k2_funct_1(A_158))=k6_partfun1(k1_relat_1(A_158)) | ~v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 5.62/2.11  tff(c_2673, plain, (![A_214]: (k6_partfun1(k1_relat_1(k2_funct_1(A_214)))=k5_relat_1(k2_funct_1(A_214), A_214) | ~v2_funct_1(k2_funct_1(A_214)) | ~v1_funct_1(k2_funct_1(A_214)) | ~v1_relat_1(k2_funct_1(A_214)) | ~v2_funct_1(A_214) | ~v1_funct_1(A_214) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2008])).
% 5.62/2.11  tff(c_2733, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2337, c_2673])).
% 5.62/2.11  tff(c_2747, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1929, c_62, c_2034, c_2284, c_2151, c_2282, c_2733])).
% 5.62/2.11  tff(c_34, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_2304, plain, (![D_205, B_204, A_206, F_202, C_201, E_203]: (k1_partfun1(A_206, B_204, C_201, D_205, E_203, F_202)=k5_relat_1(E_203, F_202) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_201, D_205))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_204))) | ~v1_funct_1(E_203))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.62/2.11  tff(c_2312, plain, (![A_206, B_204, E_203]: (k1_partfun1(A_206, B_204, '#skF_2', '#skF_2', E_203, '#skF_3')=k5_relat_1(E_203, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_204))) | ~v1_funct_1(E_203))), inference(resolution, [status(thm)], [c_56, c_2304])).
% 5.62/2.11  tff(c_2342, plain, (![A_207, B_208, E_209]: (k1_partfun1(A_207, B_208, '#skF_2', '#skF_2', E_209, '#skF_3')=k5_relat_1(E_209, '#skF_3') | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_1(E_209))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2312])).
% 5.62/2.11  tff(c_2987, plain, (![A_218, B_219]: (k1_partfun1(A_218, A_218, '#skF_2', '#skF_2', k2_funct_2(A_218, B_219), '#skF_3')=k5_relat_1(k2_funct_2(A_218, B_219), '#skF_3') | ~v1_funct_1(k2_funct_2(A_218, B_219)) | ~m1_subset_1(B_219, k1_zfmisc_1(k2_zfmisc_1(A_218, A_218))) | ~v3_funct_2(B_219, A_218, A_218) | ~v1_funct_2(B_219, A_218, A_218) | ~v1_funct_1(B_219))), inference(resolution, [status(thm)], [c_34, c_2342])).
% 5.62/2.11  tff(c_2997, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2987])).
% 5.62/2.11  tff(c_3011, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2151, c_2149, c_2747, c_2149, c_2149, c_2997])).
% 5.62/2.11  tff(c_218, plain, (![A_65, B_66, C_67, D_68]: (r2_relset_1(A_65, B_66, C_67, C_67) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.62/2.11  tff(c_228, plain, (![A_69, C_70]: (r2_relset_1(A_69, A_69, C_70, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))))), inference(resolution, [status(thm)], [c_44, c_218])).
% 5.62/2.11  tff(c_236, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_44, c_228])).
% 5.62/2.11  tff(c_81, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.62/2.11  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_81])).
% 5.62/2.11  tff(c_184, plain, (![C_57, A_58, B_59]: (v2_funct_1(C_57) | ~v3_funct_2(C_57, A_58, B_59) | ~v1_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.62/2.11  tff(c_190, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_184])).
% 5.62/2.11  tff(c_198, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_190])).
% 5.62/2.11  tff(c_300, plain, (![A_83, B_84]: (k2_funct_2(A_83, B_84)=k2_funct_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.62/2.11  tff(c_306, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_300])).
% 5.62/2.11  tff(c_314, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_306])).
% 5.62/2.11  tff(c_267, plain, (![A_74, B_75]: (v1_funct_1(k2_funct_2(A_74, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_zfmisc_1(A_74, A_74))) | ~v3_funct_2(B_75, A_74, A_74) | ~v1_funct_2(B_75, A_74, A_74) | ~v1_funct_1(B_75))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_273, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_267])).
% 5.62/2.11  tff(c_281, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_273])).
% 5.62/2.11  tff(c_316, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_281])).
% 5.62/2.11  tff(c_322, plain, (![A_85, B_86]: (v1_funct_2(k2_funct_2(A_85, B_86), A_85, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_326, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_322])).
% 5.62/2.11  tff(c_333, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_314, c_326])).
% 5.62/2.11  tff(c_339, plain, (![A_93, B_94]: (v3_funct_2(k2_funct_2(A_93, B_94), A_93, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_343, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_339])).
% 5.62/2.11  tff(c_350, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_314, c_343])).
% 5.62/2.11  tff(c_354, plain, (![A_97, B_98]: (m1_subset_1(k2_funct_2(A_97, B_98), k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_384, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_314, c_354])).
% 5.62/2.11  tff(c_396, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_384])).
% 5.62/2.11  tff(c_48, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.62/2.11  tff(c_403, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_396, c_48])).
% 5.62/2.11  tff(c_432, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_333, c_350, c_403])).
% 5.62/2.11  tff(c_40, plain, (![A_20, B_21]: (v1_funct_1(k2_funct_2(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_408, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_396, c_40])).
% 5.62/2.11  tff(c_436, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_333, c_350, c_408])).
% 5.62/2.11  tff(c_473, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_436])).
% 5.62/2.11  tff(c_38, plain, (![A_20, B_21]: (v1_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_400, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_396, c_38])).
% 5.62/2.11  tff(c_429, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_333, c_350, c_400])).
% 5.62/2.11  tff(c_520, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_429])).
% 5.62/2.11  tff(c_477, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_432, c_34])).
% 5.62/2.11  tff(c_481, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_333, c_350, c_396, c_477])).
% 5.62/2.11  tff(c_550, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_481, c_52])).
% 5.62/2.11  tff(c_587, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_520, c_550])).
% 5.62/2.11  tff(c_594, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_481, c_24])).
% 5.62/2.11  tff(c_815, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_594])).
% 5.62/2.11  tff(c_595, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_481, c_22])).
% 5.62/2.11  tff(c_36, plain, (![A_20, B_21]: (v3_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.62/2.11  tff(c_398, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_396, c_36])).
% 5.62/2.11  tff(c_426, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_333, c_350, c_398])).
% 5.62/2.11  tff(c_514, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_426])).
% 5.62/2.11  tff(c_556, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_481, c_30])).
% 5.62/2.11  tff(c_593, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_514, c_556])).
% 5.62/2.11  tff(c_542, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_481, c_48])).
% 5.62/2.11  tff(c_580, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_520, c_514, c_542])).
% 5.62/2.11  tff(c_711, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_580])).
% 5.62/2.11  tff(c_717, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_198, c_314, c_711])).
% 5.62/2.11  tff(c_63, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_partfun1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 5.62/2.11  tff(c_749, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_717, c_63])).
% 5.62/2.11  tff(c_776, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_595, c_473, c_593, c_749])).
% 5.62/2.11  tff(c_825, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_776])).
% 5.62/2.11  tff(c_836, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_825])).
% 5.62/2.11  tff(c_844, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_198, c_836])).
% 5.62/2.11  tff(c_448, plain, (![C_99, D_103, B_102, A_104, F_100, E_101]: (k1_partfun1(A_104, B_102, C_99, D_103, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_103))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.62/2.11  tff(c_450, plain, (![A_104, B_102, E_101]: (k1_partfun1(A_104, B_102, '#skF_2', '#skF_2', E_101, k2_funct_1('#skF_3'))=k5_relat_1(E_101, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(resolution, [status(thm)], [c_396, c_448])).
% 5.62/2.11  tff(c_1857, plain, (![A_138, B_139, E_140]: (k1_partfun1(A_138, B_139, '#skF_2', '#skF_2', E_140, k2_funct_1('#skF_3'))=k5_relat_1(E_140, k2_funct_1('#skF_3')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_450])).
% 5.62/2.11  tff(c_1887, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1857])).
% 5.62/2.11  tff(c_1907, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_844, c_1887])).
% 5.62/2.11  tff(c_54, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.62/2.11  tff(c_78, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.62/2.11  tff(c_317, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_78])).
% 5.62/2.11  tff(c_1909, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_317])).
% 5.62/2.11  tff(c_1912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_1909])).
% 5.62/2.11  tff(c_1913, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 5.62/2.11  tff(c_2153, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2149, c_1913])).
% 5.62/2.11  tff(c_3067, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3011, c_2153])).
% 5.62/2.11  tff(c_3070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2099, c_3067])).
% 5.62/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.11  
% 5.62/2.11  Inference rules
% 5.62/2.11  ----------------------
% 5.62/2.11  #Ref     : 0
% 5.62/2.11  #Sup     : 729
% 5.62/2.11  #Fact    : 0
% 5.62/2.11  #Define  : 0
% 5.62/2.11  #Split   : 2
% 5.62/2.11  #Chain   : 0
% 5.62/2.11  #Close   : 0
% 5.62/2.11  
% 5.62/2.11  Ordering : KBO
% 5.62/2.11  
% 5.62/2.11  Simplification rules
% 5.62/2.11  ----------------------
% 5.62/2.11  #Subsume      : 78
% 5.62/2.11  #Demod        : 1231
% 5.62/2.11  #Tautology    : 299
% 5.62/2.11  #SimpNegUnit  : 0
% 5.62/2.11  #BackRed      : 26
% 5.62/2.11  
% 5.62/2.11  #Partial instantiations: 0
% 5.62/2.11  #Strategies tried      : 1
% 5.62/2.11  
% 5.62/2.11  Timing (in seconds)
% 5.62/2.11  ----------------------
% 5.62/2.11  Preprocessing        : 0.36
% 5.62/2.11  Parsing              : 0.19
% 5.62/2.11  CNF conversion       : 0.02
% 5.62/2.11  Main loop            : 0.90
% 5.62/2.11  Inferencing          : 0.29
% 5.62/2.11  Reduction            : 0.34
% 5.62/2.11  Demodulation         : 0.26
% 5.62/2.11  BG Simplification    : 0.04
% 5.62/2.11  Subsumption          : 0.14
% 5.62/2.11  Abstraction          : 0.04
% 5.62/2.11  MUC search           : 0.00
% 5.62/2.11  Cooper               : 0.00
% 5.62/2.11  Total                : 1.31
% 5.62/2.11  Index Insertion      : 0.00
% 5.62/2.11  Index Deletion       : 0.00
% 5.62/2.11  Index Matching       : 0.00
% 5.62/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
