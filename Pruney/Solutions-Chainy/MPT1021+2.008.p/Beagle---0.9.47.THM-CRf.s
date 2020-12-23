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
% DateTime   : Thu Dec  3 10:16:00 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  187 (8141 expanded)
%              Number of leaves         :   43 (3291 expanded)
%              Depth                    :   22
%              Number of atoms          :  467 (29791 expanded)
%              Number of equality atoms :   62 (1507 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

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
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2220,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( r2_relset_1(A_179,B_180,C_181,C_181)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2242,plain,(
    ! [A_184,B_185,C_186] :
      ( r2_relset_1(A_184,B_185,C_186,C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(resolution,[status(thm)],[c_4,c_2220])).

tff(c_2250,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_40,c_2242])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2069,plain,(
    ! [B_152,A_153] :
      ( v1_relat_1(B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2075,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_2069])).

tff(c_2084,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2075])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2186,plain,(
    ! [C_171,A_172,B_173] :
      ( v2_funct_1(C_171)
      | ~ v3_funct_2(C_171,A_172,B_173)
      | ~ v1_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2192,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2186])).

tff(c_2200,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2192])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2304,plain,(
    ! [A_198,B_199] :
      ( k2_funct_2(A_198,B_199) = k2_funct_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2310,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2304])).

tff(c_2318,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2310])).

tff(c_2358,plain,(
    ! [A_210,B_211] :
      ( m1_subset_1(k2_funct_2(A_210,B_211),k1_zfmisc_1(k2_zfmisc_1(A_210,A_210)))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(A_210,A_210)))
      | ~ v3_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2391,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_2358])).

tff(c_2406,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2391])).

tff(c_18,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2460,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2406,c_18])).

tff(c_2283,plain,(
    ! [A_190,B_191] :
      ( v1_funct_1(k2_funct_2(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2289,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2283])).

tff(c_2297,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2289])).

tff(c_2320,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2318,c_2297])).

tff(c_2330,plain,(
    ! [A_204,B_205] :
      ( v3_funct_2(k2_funct_2(A_204,B_205),A_204,A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(k2_zfmisc_1(A_204,A_204)))
      | ~ v3_funct_2(B_205,A_204,A_204)
      | ~ v1_funct_2(B_205,A_204,A_204)
      | ~ v1_funct_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2334,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2330])).

tff(c_2341,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2318,c_2334])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22] :
      ( v2_funct_1(C_23)
      | ~ v3_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2427,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2406,c_26])).

tff(c_2458,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2320,c_2341,c_2427])).

tff(c_2343,plain,(
    ! [A_206,B_207] :
      ( v1_funct_2(k2_funct_2(A_206,B_207),A_206,A_206)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2347,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2343])).

tff(c_2354,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2318,c_2347])).

tff(c_48,plain,(
    ! [A_36,B_37] :
      ( k1_relset_1(A_36,A_36,B_37) = A_36
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k2_zfmisc_1(A_36,A_36)))
      | ~ v1_funct_2(B_37,A_36,A_36)
      | ~ v1_funct_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2419,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2406,c_48])).

tff(c_2451,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2320,c_2354,c_2419])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2459,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2406,c_20])).

tff(c_2543,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_2459])).

tff(c_16,plain,(
    ! [A_10] :
      ( k2_funct_1(k2_funct_1(A_10)) = A_10
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_12,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2174,plain,(
    ! [A_170] :
      ( k5_relat_1(A_170,k2_funct_1(A_170)) = k6_partfun1(k1_relat_1(A_170))
      | ~ v2_funct_1(A_170)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_3261,plain,(
    ! [A_233] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_233))) = k5_relat_1(k2_funct_1(A_233),A_233)
      | ~ v2_funct_1(k2_funct_1(A_233))
      | ~ v1_funct_1(k2_funct_1(A_233))
      | ~ v1_relat_1(k2_funct_1(A_233))
      | ~ v2_funct_1(A_233)
      | ~ v1_funct_1(A_233)
      | ~ v1_relat_1(A_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2174])).

tff(c_3329,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2543,c_3261])).

tff(c_3347,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_58,c_2200,c_2460,c_2320,c_2458,c_3329])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_funct_2(A_24,B_25),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2465,plain,(
    ! [A_217,B_216,C_213,D_214,F_212,E_215] :
      ( k1_partfun1(A_217,B_216,C_213,D_214,E_215,F_212) = k5_relat_1(E_215,F_212)
      | ~ m1_subset_1(F_212,k1_zfmisc_1(k2_zfmisc_1(C_213,D_214)))
      | ~ v1_funct_1(F_212)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216)))
      | ~ v1_funct_1(E_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2473,plain,(
    ! [A_217,B_216,E_215] :
      ( k1_partfun1(A_217,B_216,'#skF_2','#skF_2',E_215,'#skF_3') = k5_relat_1(E_215,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216)))
      | ~ v1_funct_1(E_215) ) ),
    inference(resolution,[status(thm)],[c_52,c_2465])).

tff(c_2490,plain,(
    ! [A_218,B_219,E_220] :
      ( k1_partfun1(A_218,B_219,'#skF_2','#skF_2',E_220,'#skF_3') = k5_relat_1(E_220,'#skF_3')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_1(E_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2473])).

tff(c_3031,plain,(
    ! [A_231,B_232] :
      ( k1_partfun1(A_231,A_231,'#skF_2','#skF_2',k2_funct_2(A_231,B_232),'#skF_3') = k5_relat_1(k2_funct_2(A_231,B_232),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_231,B_232))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k2_zfmisc_1(A_231,A_231)))
      | ~ v3_funct_2(B_232,A_231,A_231)
      | ~ v1_funct_2(B_232,A_231,A_231)
      | ~ v1_funct_1(B_232) ) ),
    inference(resolution,[status(thm)],[c_30,c_2490])).

tff(c_3041,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3031])).

tff(c_3055,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2320,c_2318,c_2318,c_2318,c_3041])).

tff(c_3420,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3347,c_3055])).

tff(c_254,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( r2_relset_1(A_74,B_75,C_76,C_76)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_264,plain,(
    ! [A_78,C_79] :
      ( r2_relset_1(A_78,A_78,C_79,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,A_78))) ) ),
    inference(resolution,[status(thm)],[c_40,c_254])).

tff(c_272,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_40,c_264])).

tff(c_76,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_193,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_funct_1(C_64)
      | ~ v3_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_199,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_193])).

tff(c_207,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_199])).

tff(c_312,plain,(
    ! [A_95,B_96] :
      ( k2_funct_2(A_95,B_96) = k2_funct_1(B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_318,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_312])).

tff(c_326,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_318])).

tff(c_514,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k2_funct_2(A_109,B_110),k1_zfmisc_1(k2_zfmisc_1(A_109,A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(A_109,A_109)))
      | ~ v3_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_547,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_514])).

tff(c_562,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_547])).

tff(c_616,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_18])).

tff(c_294,plain,(
    ! [A_90,B_91] :
      ( v1_funct_1(k2_funct_2(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_90,A_90)))
      | ~ v3_funct_2(B_91,A_90,A_90)
      | ~ v1_funct_2(B_91,A_90,A_90)
      | ~ v1_funct_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_300,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_294])).

tff(c_308,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_300])).

tff(c_328,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_308])).

tff(c_350,plain,(
    ! [A_102,B_103] :
      ( v3_funct_2(k2_funct_2(A_102,B_103),A_102,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_354,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_350])).

tff(c_361,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_326,c_354])).

tff(c_583,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_26])).

tff(c_614,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_361,c_583])).

tff(c_10,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [A_62] :
      ( k5_relat_1(k2_funct_1(A_62),A_62) = k6_partfun1(k2_relat_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_178,plain,(
    ! [A_10] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_10))) = k5_relat_1(A_10,k2_funct_1(A_10))
      | ~ v2_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_169])).

tff(c_336,plain,(
    ! [A_99,B_100] :
      ( v1_funct_2(k2_funct_2(A_99,B_100),A_99,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_340,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_336])).

tff(c_347,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_326,c_340])).

tff(c_44,plain,(
    ! [A_33,B_34] :
      ( k2_funct_2(A_33,B_34) = k2_funct_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v3_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_569,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_44])).

tff(c_601,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_569])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_544,plain,(
    ! [A_109,B_110] :
      ( v1_relat_1(k2_funct_2(A_109,B_110))
      | ~ v1_relat_1(k2_zfmisc_1(A_109,A_109))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k2_zfmisc_1(A_109,A_109)))
      | ~ v3_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_2(B_110,A_109,A_109)
      | ~ v1_funct_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_514,c_6])).

tff(c_781,plain,(
    ! [A_120,B_121] :
      ( v1_relat_1(k2_funct_2(A_120,B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_zfmisc_1(A_120,A_120)))
      | ~ v3_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_544])).

tff(c_784,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_781])).

tff(c_800,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_601,c_784])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( v1_funct_1(k2_funct_2(A_24,B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_572,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_36])).

tff(c_604,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_572])).

tff(c_625,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_604])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( v3_funct_2(k2_funct_2(A_24,B_25),A_24,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_564,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_32])).

tff(c_595,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_564])).

tff(c_661,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_595])).

tff(c_629,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_30])).

tff(c_633,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_562,c_629])).

tff(c_840,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_633,c_26])).

tff(c_883,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_661,c_840])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( v1_funct_2(k2_funct_2(A_24,B_25),A_24,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_566,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_34])).

tff(c_598,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_566])).

tff(c_667,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_598])).

tff(c_834,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_633,c_48])).

tff(c_877,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_667,c_834])).

tff(c_1294,plain,(
    ! [A_130,B_131] :
      ( k1_relset_1(A_130,A_130,k2_funct_2(A_130,B_131)) = k1_relat_1(k2_funct_2(A_130,B_131))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_zfmisc_1(A_130,A_130)))
      | ~ v3_funct_2(B_131,A_130,A_130)
      | ~ v1_funct_2(B_131,A_130,A_130)
      | ~ v1_funct_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_514,c_20])).

tff(c_1300,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_1294])).

tff(c_1316,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_347,c_361,c_877,c_601,c_601,c_1300])).

tff(c_826,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_633,c_44])).

tff(c_870,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_667,c_661,c_826])).

tff(c_974,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_870])).

tff(c_980,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_207,c_326,c_974])).

tff(c_1012,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_178])).

tff(c_1045,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_625,c_883,c_616,c_980,c_328,c_980,c_614,c_980,c_980,c_1012])).

tff(c_181,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k2_funct_1(A_63)) = k6_partfun1(k1_relat_1(A_63))
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_190,plain,(
    ! [A_10] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_10))) = k5_relat_1(k2_funct_1(A_10),A_10)
      | ~ v2_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_181])).

tff(c_1380,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_190])).

tff(c_1398,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_328,c_614,c_800,c_625,c_883,c_1316,c_1380])).

tff(c_1459,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_1398])).

tff(c_1478,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_207,c_616,c_328,c_614,c_1459])).

tff(c_635,plain,(
    ! [B_115,A_116,D_113,C_112,E_114,F_111] :
      ( k1_partfun1(A_116,B_115,C_112,D_113,E_114,F_111) = k5_relat_1(E_114,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_112,D_113)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_637,plain,(
    ! [A_116,B_115,E_114] :
      ( k1_partfun1(A_116,B_115,'#skF_2','#skF_2',E_114,k2_funct_1('#skF_3')) = k5_relat_1(E_114,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115)))
      | ~ v1_funct_1(E_114) ) ),
    inference(resolution,[status(thm)],[c_562,c_635])).

tff(c_2010,plain,(
    ! [A_148,B_149,E_150] :
      ( k1_partfun1(A_148,B_149,'#skF_2','#skF_2',E_150,k2_funct_1('#skF_3')) = k5_relat_1(E_150,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_1(E_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_637])).

tff(c_2040,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2010])).

tff(c_2060,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1478,c_2040])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_329,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_74])).

tff(c_2062,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2060,c_329])).

tff(c_2065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_2062])).

tff(c_2066,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2322,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2318,c_2066])).

tff(c_3421,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3420,c_2322])).

tff(c_3424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_3421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.04  
% 5.37/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.04  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.37/2.04  
% 5.37/2.04  %Foreground sorts:
% 5.37/2.04  
% 5.37/2.04  
% 5.37/2.04  %Background operators:
% 5.37/2.04  
% 5.37/2.04  
% 5.37/2.04  %Foreground operators:
% 5.37/2.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.37/2.04  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.37/2.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.37/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.04  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.37/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.37/2.04  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.37/2.04  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.37/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.37/2.04  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.37/2.04  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.37/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.04  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.37/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.04  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.37/2.04  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.37/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.37/2.04  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.37/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.37/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.37/2.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.37/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.04  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.37/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.37/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.37/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.37/2.04  
% 5.71/2.07  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.71/2.07  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 5.71/2.07  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.71/2.07  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.71/2.07  tff(f_154, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.71/2.07  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.71/2.07  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.71/2.07  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.71/2.07  tff(f_107, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.71/2.07  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.71/2.07  tff(f_141, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.71/2.07  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.71/2.07  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.71/2.07  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.71/2.07  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.71/2.07  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.71/2.07  tff(c_40, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.71/2.07  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.71/2.07  tff(c_2220, plain, (![A_179, B_180, C_181, D_182]: (r2_relset_1(A_179, B_180, C_181, C_181) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.71/2.07  tff(c_2242, plain, (![A_184, B_185, C_186]: (r2_relset_1(A_184, B_185, C_186, C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(resolution, [status(thm)], [c_4, c_2220])).
% 5.71/2.07  tff(c_2250, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_40, c_2242])).
% 5.71/2.07  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.71/2.07  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.71/2.07  tff(c_2069, plain, (![B_152, A_153]: (v1_relat_1(B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.71/2.07  tff(c_2075, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_2069])).
% 5.71/2.07  tff(c_2084, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2075])).
% 5.71/2.07  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.71/2.07  tff(c_54, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.71/2.07  tff(c_2186, plain, (![C_171, A_172, B_173]: (v2_funct_1(C_171) | ~v3_funct_2(C_171, A_172, B_173) | ~v1_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.07  tff(c_2192, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2186])).
% 5.71/2.07  tff(c_2200, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2192])).
% 5.71/2.07  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.71/2.07  tff(c_2304, plain, (![A_198, B_199]: (k2_funct_2(A_198, B_199)=k2_funct_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.71/2.07  tff(c_2310, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2304])).
% 5.71/2.07  tff(c_2318, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2310])).
% 5.71/2.07  tff(c_2358, plain, (![A_210, B_211]: (m1_subset_1(k2_funct_2(A_210, B_211), k1_zfmisc_1(k2_zfmisc_1(A_210, A_210))) | ~m1_subset_1(B_211, k1_zfmisc_1(k2_zfmisc_1(A_210, A_210))) | ~v3_funct_2(B_211, A_210, A_210) | ~v1_funct_2(B_211, A_210, A_210) | ~v1_funct_1(B_211))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_2391, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2318, c_2358])).
% 5.71/2.07  tff(c_2406, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2391])).
% 5.71/2.07  tff(c_18, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.71/2.07  tff(c_2460, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2406, c_18])).
% 5.71/2.07  tff(c_2283, plain, (![A_190, B_191]: (v1_funct_1(k2_funct_2(A_190, B_191)) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_2289, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2283])).
% 5.71/2.07  tff(c_2297, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2289])).
% 5.71/2.07  tff(c_2320, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2318, c_2297])).
% 5.71/2.07  tff(c_2330, plain, (![A_204, B_205]: (v3_funct_2(k2_funct_2(A_204, B_205), A_204, A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(k2_zfmisc_1(A_204, A_204))) | ~v3_funct_2(B_205, A_204, A_204) | ~v1_funct_2(B_205, A_204, A_204) | ~v1_funct_1(B_205))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_2334, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2330])).
% 5.71/2.07  tff(c_2341, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2318, c_2334])).
% 5.71/2.07  tff(c_26, plain, (![C_23, A_21, B_22]: (v2_funct_1(C_23) | ~v3_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.07  tff(c_2427, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2406, c_26])).
% 5.71/2.07  tff(c_2458, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2320, c_2341, c_2427])).
% 5.71/2.07  tff(c_2343, plain, (![A_206, B_207]: (v1_funct_2(k2_funct_2(A_206, B_207), A_206, A_206) | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_207, A_206, A_206) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_2347, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2343])).
% 5.71/2.07  tff(c_2354, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2318, c_2347])).
% 5.71/2.07  tff(c_48, plain, (![A_36, B_37]: (k1_relset_1(A_36, A_36, B_37)=A_36 | ~m1_subset_1(B_37, k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))) | ~v1_funct_2(B_37, A_36, A_36) | ~v1_funct_1(B_37))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.71/2.07  tff(c_2419, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2406, c_48])).
% 5.71/2.07  tff(c_2451, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2320, c_2354, c_2419])).
% 5.71/2.07  tff(c_20, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.71/2.07  tff(c_2459, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2406, c_20])).
% 5.71/2.07  tff(c_2543, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_2459])).
% 5.71/2.07  tff(c_16, plain, (![A_10]: (k2_funct_1(k2_funct_1(A_10))=A_10 | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.71/2.07  tff(c_46, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.71/2.07  tff(c_12, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.07  tff(c_2174, plain, (![A_170]: (k5_relat_1(A_170, k2_funct_1(A_170))=k6_partfun1(k1_relat_1(A_170)) | ~v2_funct_1(A_170) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.71/2.07  tff(c_3261, plain, (![A_233]: (k6_partfun1(k1_relat_1(k2_funct_1(A_233)))=k5_relat_1(k2_funct_1(A_233), A_233) | ~v2_funct_1(k2_funct_1(A_233)) | ~v1_funct_1(k2_funct_1(A_233)) | ~v1_relat_1(k2_funct_1(A_233)) | ~v2_funct_1(A_233) | ~v1_funct_1(A_233) | ~v1_relat_1(A_233))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2174])).
% 5.71/2.07  tff(c_3329, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2543, c_3261])).
% 5.71/2.07  tff(c_3347, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_58, c_2200, c_2460, c_2320, c_2458, c_3329])).
% 5.71/2.07  tff(c_30, plain, (![A_24, B_25]: (m1_subset_1(k2_funct_2(A_24, B_25), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_2465, plain, (![A_217, B_216, C_213, D_214, F_212, E_215]: (k1_partfun1(A_217, B_216, C_213, D_214, E_215, F_212)=k5_relat_1(E_215, F_212) | ~m1_subset_1(F_212, k1_zfmisc_1(k2_zfmisc_1(C_213, D_214))) | ~v1_funct_1(F_212) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))) | ~v1_funct_1(E_215))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.07  tff(c_2473, plain, (![A_217, B_216, E_215]: (k1_partfun1(A_217, B_216, '#skF_2', '#skF_2', E_215, '#skF_3')=k5_relat_1(E_215, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))) | ~v1_funct_1(E_215))), inference(resolution, [status(thm)], [c_52, c_2465])).
% 5.71/2.07  tff(c_2490, plain, (![A_218, B_219, E_220]: (k1_partfun1(A_218, B_219, '#skF_2', '#skF_2', E_220, '#skF_3')=k5_relat_1(E_220, '#skF_3') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_1(E_220))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2473])).
% 5.71/2.07  tff(c_3031, plain, (![A_231, B_232]: (k1_partfun1(A_231, A_231, '#skF_2', '#skF_2', k2_funct_2(A_231, B_232), '#skF_3')=k5_relat_1(k2_funct_2(A_231, B_232), '#skF_3') | ~v1_funct_1(k2_funct_2(A_231, B_232)) | ~m1_subset_1(B_232, k1_zfmisc_1(k2_zfmisc_1(A_231, A_231))) | ~v3_funct_2(B_232, A_231, A_231) | ~v1_funct_2(B_232, A_231, A_231) | ~v1_funct_1(B_232))), inference(resolution, [status(thm)], [c_30, c_2490])).
% 5.71/2.07  tff(c_3041, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3031])).
% 5.71/2.07  tff(c_3055, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2320, c_2318, c_2318, c_2318, c_3041])).
% 5.71/2.07  tff(c_3420, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3347, c_3055])).
% 5.71/2.07  tff(c_254, plain, (![A_74, B_75, C_76, D_77]: (r2_relset_1(A_74, B_75, C_76, C_76) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.71/2.07  tff(c_264, plain, (![A_78, C_79]: (r2_relset_1(A_78, A_78, C_79, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, A_78))))), inference(resolution, [status(thm)], [c_40, c_254])).
% 5.71/2.07  tff(c_272, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_40, c_264])).
% 5.71/2.07  tff(c_76, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.71/2.07  tff(c_82, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_76])).
% 5.71/2.07  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_82])).
% 5.71/2.07  tff(c_193, plain, (![C_64, A_65, B_66]: (v2_funct_1(C_64) | ~v3_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.07  tff(c_199, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_193])).
% 5.71/2.07  tff(c_207, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_199])).
% 5.71/2.07  tff(c_312, plain, (![A_95, B_96]: (k2_funct_2(A_95, B_96)=k2_funct_1(B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.71/2.07  tff(c_318, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_312])).
% 5.71/2.07  tff(c_326, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_318])).
% 5.71/2.07  tff(c_514, plain, (![A_109, B_110]: (m1_subset_1(k2_funct_2(A_109, B_110), k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))) | ~v3_funct_2(B_110, A_109, A_109) | ~v1_funct_2(B_110, A_109, A_109) | ~v1_funct_1(B_110))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_547, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_514])).
% 5.71/2.07  tff(c_562, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_547])).
% 5.71/2.07  tff(c_616, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_18])).
% 5.71/2.07  tff(c_294, plain, (![A_90, B_91]: (v1_funct_1(k2_funct_2(A_90, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(A_90, A_90))) | ~v3_funct_2(B_91, A_90, A_90) | ~v1_funct_2(B_91, A_90, A_90) | ~v1_funct_1(B_91))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_300, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_294])).
% 5.71/2.07  tff(c_308, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_300])).
% 5.71/2.07  tff(c_328, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_308])).
% 5.71/2.07  tff(c_350, plain, (![A_102, B_103]: (v3_funct_2(k2_funct_2(A_102, B_103), A_102, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_354, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_350])).
% 5.71/2.07  tff(c_361, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_326, c_354])).
% 5.71/2.07  tff(c_583, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_26])).
% 5.71/2.07  tff(c_614, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_361, c_583])).
% 5.71/2.07  tff(c_10, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.07  tff(c_169, plain, (![A_62]: (k5_relat_1(k2_funct_1(A_62), A_62)=k6_partfun1(k2_relat_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 5.71/2.07  tff(c_178, plain, (![A_10]: (k6_partfun1(k2_relat_1(k2_funct_1(A_10)))=k5_relat_1(A_10, k2_funct_1(A_10)) | ~v2_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_169])).
% 5.71/2.07  tff(c_336, plain, (![A_99, B_100]: (v1_funct_2(k2_funct_2(A_99, B_100), A_99, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_340, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_336])).
% 5.71/2.07  tff(c_347, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_326, c_340])).
% 5.71/2.07  tff(c_44, plain, (![A_33, B_34]: (k2_funct_2(A_33, B_34)=k2_funct_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v3_funct_2(B_34, A_33, A_33) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.71/2.07  tff(c_569, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_44])).
% 5.71/2.07  tff(c_601, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_569])).
% 5.71/2.07  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.71/2.07  tff(c_544, plain, (![A_109, B_110]: (v1_relat_1(k2_funct_2(A_109, B_110)) | ~v1_relat_1(k2_zfmisc_1(A_109, A_109)) | ~m1_subset_1(B_110, k1_zfmisc_1(k2_zfmisc_1(A_109, A_109))) | ~v3_funct_2(B_110, A_109, A_109) | ~v1_funct_2(B_110, A_109, A_109) | ~v1_funct_1(B_110))), inference(resolution, [status(thm)], [c_514, c_6])).
% 5.71/2.07  tff(c_781, plain, (![A_120, B_121]: (v1_relat_1(k2_funct_2(A_120, B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(k2_zfmisc_1(A_120, A_120))) | ~v3_funct_2(B_121, A_120, A_120) | ~v1_funct_2(B_121, A_120, A_120) | ~v1_funct_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_544])).
% 5.71/2.07  tff(c_784, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_781])).
% 5.71/2.07  tff(c_800, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_601, c_784])).
% 5.71/2.07  tff(c_36, plain, (![A_24, B_25]: (v1_funct_1(k2_funct_2(A_24, B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_572, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_36])).
% 5.71/2.07  tff(c_604, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_572])).
% 5.71/2.07  tff(c_625, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_604])).
% 5.71/2.07  tff(c_32, plain, (![A_24, B_25]: (v3_funct_2(k2_funct_2(A_24, B_25), A_24, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_564, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_32])).
% 5.71/2.07  tff(c_595, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_564])).
% 5.71/2.07  tff(c_661, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_595])).
% 5.71/2.07  tff(c_629, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_601, c_30])).
% 5.71/2.07  tff(c_633, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_562, c_629])).
% 5.71/2.07  tff(c_840, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_633, c_26])).
% 5.71/2.07  tff(c_883, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_661, c_840])).
% 5.71/2.07  tff(c_34, plain, (![A_24, B_25]: (v1_funct_2(k2_funct_2(A_24, B_25), A_24, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.71/2.07  tff(c_566, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_34])).
% 5.71/2.07  tff(c_598, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_566])).
% 5.71/2.07  tff(c_667, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_598])).
% 5.71/2.07  tff(c_834, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_633, c_48])).
% 5.71/2.07  tff(c_877, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_667, c_834])).
% 5.71/2.07  tff(c_1294, plain, (![A_130, B_131]: (k1_relset_1(A_130, A_130, k2_funct_2(A_130, B_131))=k1_relat_1(k2_funct_2(A_130, B_131)) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_zfmisc_1(A_130, A_130))) | ~v3_funct_2(B_131, A_130, A_130) | ~v1_funct_2(B_131, A_130, A_130) | ~v1_funct_1(B_131))), inference(resolution, [status(thm)], [c_514, c_20])).
% 5.71/2.07  tff(c_1300, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_2('#skF_2', k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_1294])).
% 5.71/2.07  tff(c_1316, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_328, c_347, c_361, c_877, c_601, c_601, c_1300])).
% 5.71/2.07  tff(c_826, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_633, c_44])).
% 5.71/2.07  tff(c_870, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_667, c_661, c_826])).
% 5.71/2.07  tff(c_974, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_870])).
% 5.71/2.07  tff(c_980, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_207, c_326, c_974])).
% 5.71/2.07  tff(c_1012, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_980, c_178])).
% 5.71/2.07  tff(c_1045, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_625, c_883, c_616, c_980, c_328, c_980, c_614, c_980, c_980, c_1012])).
% 5.71/2.07  tff(c_181, plain, (![A_63]: (k5_relat_1(A_63, k2_funct_1(A_63))=k6_partfun1(k1_relat_1(A_63)) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.71/2.07  tff(c_190, plain, (![A_10]: (k6_partfun1(k1_relat_1(k2_funct_1(A_10)))=k5_relat_1(k2_funct_1(A_10), A_10) | ~v2_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_181])).
% 5.71/2.07  tff(c_1380, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1045, c_190])).
% 5.71/2.07  tff(c_1398, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_328, c_614, c_800, c_625, c_883, c_1316, c_1380])).
% 5.71/2.07  tff(c_1459, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_1398])).
% 5.71/2.07  tff(c_1478, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_207, c_616, c_328, c_614, c_1459])).
% 5.71/2.07  tff(c_635, plain, (![B_115, A_116, D_113, C_112, E_114, F_111]: (k1_partfun1(A_116, B_115, C_112, D_113, E_114, F_111)=k5_relat_1(E_114, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_112, D_113))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.71/2.07  tff(c_637, plain, (![A_116, B_115, E_114]: (k1_partfun1(A_116, B_115, '#skF_2', '#skF_2', E_114, k2_funct_1('#skF_3'))=k5_relat_1(E_114, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))) | ~v1_funct_1(E_114))), inference(resolution, [status(thm)], [c_562, c_635])).
% 5.71/2.07  tff(c_2010, plain, (![A_148, B_149, E_150]: (k1_partfun1(A_148, B_149, '#skF_2', '#skF_2', E_150, k2_funct_1('#skF_3'))=k5_relat_1(E_150, k2_funct_1('#skF_3')) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_1(E_150))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_637])).
% 5.71/2.07  tff(c_2040, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2010])).
% 5.71/2.07  tff(c_2060, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1478, c_2040])).
% 5.71/2.07  tff(c_50, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.71/2.07  tff(c_74, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.71/2.07  tff(c_329, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_74])).
% 5.71/2.07  tff(c_2062, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2060, c_329])).
% 5.71/2.07  tff(c_2065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_2062])).
% 5.71/2.07  tff(c_2066, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 5.71/2.07  tff(c_2322, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2318, c_2066])).
% 5.71/2.07  tff(c_3421, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3420, c_2322])).
% 5.71/2.07  tff(c_3424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2250, c_3421])).
% 5.71/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.07  
% 5.71/2.07  Inference rules
% 5.71/2.07  ----------------------
% 5.71/2.07  #Ref     : 0
% 5.71/2.07  #Sup     : 804
% 5.71/2.07  #Fact    : 0
% 5.71/2.07  #Define  : 0
% 5.71/2.07  #Split   : 2
% 5.71/2.07  #Chain   : 0
% 5.71/2.07  #Close   : 0
% 5.71/2.07  
% 5.71/2.07  Ordering : KBO
% 5.71/2.07  
% 5.71/2.07  Simplification rules
% 5.71/2.07  ----------------------
% 5.71/2.07  #Subsume      : 85
% 5.71/2.07  #Demod        : 1479
% 5.71/2.07  #Tautology    : 344
% 5.71/2.07  #SimpNegUnit  : 0
% 5.71/2.07  #BackRed      : 36
% 5.71/2.07  
% 5.71/2.07  #Partial instantiations: 0
% 5.71/2.07  #Strategies tried      : 1
% 5.71/2.07  
% 5.71/2.07  Timing (in seconds)
% 5.71/2.07  ----------------------
% 5.78/2.08  Preprocessing        : 0.34
% 5.78/2.08  Parsing              : 0.18
% 5.78/2.08  CNF conversion       : 0.02
% 5.78/2.08  Main loop            : 0.90
% 5.78/2.08  Inferencing          : 0.30
% 5.78/2.08  Reduction            : 0.35
% 5.78/2.08  Demodulation         : 0.27
% 5.78/2.08  BG Simplification    : 0.04
% 5.78/2.08  Subsumption          : 0.14
% 5.78/2.08  Abstraction          : 0.04
% 5.78/2.08  MUC search           : 0.00
% 5.78/2.08  Cooper               : 0.00
% 5.78/2.08  Total                : 1.31
% 5.78/2.08  Index Insertion      : 0.00
% 5.78/2.08  Index Deletion       : 0.00
% 5.78/2.08  Index Matching       : 0.00
% 5.78/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
