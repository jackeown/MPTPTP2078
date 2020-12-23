%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:00 EST 2020

% Result     : Theorem 5.33s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :  185 (8040 expanded)
%              Number of leaves         :   42 (3249 expanded)
%              Depth                    :   22
%              Number of atoms          :  458 (29415 expanded)
%              Number of equality atoms :   61 (1486 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_97,axiom,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_36,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2168,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( r2_relset_1(A_174,B_175,C_176,C_176)
      | ~ m1_subset_1(D_177,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2190,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_relset_1(A_179,B_180,C_181,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(resolution,[status(thm)],[c_2,c_2168])).

tff(c_2198,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_36,c_2190])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2020,plain,(
    ! [B_148,A_149] :
      ( v1_relat_1(B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_149))
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2026,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_2020])).

tff(c_2036,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2026])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2125,plain,(
    ! [C_164,A_165,B_166] :
      ( v2_funct_1(C_164)
      | ~ v3_funct_2(C_164,A_165,B_166)
      | ~ v1_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2131,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2125])).

tff(c_2139,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2131])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2252,plain,(
    ! [A_193,B_194] :
      ( k2_funct_2(A_193,B_194) = k2_funct_1(B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2258,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2252])).

tff(c_2266,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2258])).

tff(c_2306,plain,(
    ! [A_205,B_206] :
      ( m1_subset_1(k2_funct_2(A_205,B_206),k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2339,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2266,c_2306])).

tff(c_2354,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2339])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2408,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2354,c_14])).

tff(c_2234,plain,(
    ! [A_188,B_189] :
      ( v1_funct_1(k2_funct_2(A_188,B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2240,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2234])).

tff(c_2248,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2240])).

tff(c_2268,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_2248])).

tff(c_2291,plain,(
    ! [A_201,B_202] :
      ( v3_funct_2(k2_funct_2(A_201,B_202),A_201,A_201)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_zfmisc_1(A_201,A_201)))
      | ~ v3_funct_2(B_202,A_201,A_201)
      | ~ v1_funct_2(B_202,A_201,A_201)
      | ~ v1_funct_1(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2295,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2291])).

tff(c_2302,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2266,c_2295])).

tff(c_22,plain,(
    ! [C_22,A_20,B_21] :
      ( v2_funct_1(C_22)
      | ~ v3_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2375,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2354,c_22])).

tff(c_2406,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_2302,c_2375])).

tff(c_2278,plain,(
    ! [A_199,B_200] :
      ( v1_funct_2(k2_funct_2(A_199,B_200),A_199,A_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(A_199,A_199)))
      | ~ v3_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_2(B_200,A_199,A_199)
      | ~ v1_funct_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2282,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2278])).

tff(c_2289,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2266,c_2282])).

tff(c_44,plain,(
    ! [A_35,B_36] :
      ( k1_relset_1(A_35,A_35,B_36) = A_35
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_zfmisc_1(A_35,A_35)))
      | ~ v1_funct_2(B_36,A_35,A_35)
      | ~ v1_funct_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2367,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2354,c_44])).

tff(c_2399,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_2289,c_2367])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] :
      ( k1_relset_1(A_13,B_14,C_15) = k1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2407,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2354,c_16])).

tff(c_2491,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2399,c_2407])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_funct_1(k2_funct_1(A_9)) = A_9
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_10,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2113,plain,(
    ! [A_163] :
      ( k5_relat_1(A_163,k2_funct_1(A_163)) = k6_partfun1(k1_relat_1(A_163))
      | ~ v2_funct_1(A_163)
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_3204,plain,(
    ! [A_228] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_228))) = k5_relat_1(k2_funct_1(A_228),A_228)
      | ~ v2_funct_1(k2_funct_1(A_228))
      | ~ v1_funct_1(k2_funct_1(A_228))
      | ~ v1_relat_1(k2_funct_1(A_228))
      | ~ v2_funct_1(A_228)
      | ~ v1_funct_1(A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2113])).

tff(c_3272,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2491,c_3204])).

tff(c_3290,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2036,c_54,c_2139,c_2408,c_2268,c_2406,c_3272])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_funct_2(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2413,plain,(
    ! [B_208,C_211,A_209,F_210,E_212,D_207] :
      ( k1_partfun1(A_209,B_208,C_211,D_207,E_212,F_210) = k5_relat_1(E_212,F_210)
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(C_211,D_207)))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208)))
      | ~ v1_funct_1(E_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2421,plain,(
    ! [A_209,B_208,E_212] :
      ( k1_partfun1(A_209,B_208,'#skF_2','#skF_2',E_212,'#skF_3') = k5_relat_1(E_212,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208)))
      | ~ v1_funct_1(E_212) ) ),
    inference(resolution,[status(thm)],[c_48,c_2413])).

tff(c_2438,plain,(
    ! [A_213,B_214,E_215] :
      ( k1_partfun1(A_213,B_214,'#skF_2','#skF_2',E_215,'#skF_3') = k5_relat_1(E_215,'#skF_3')
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_1(E_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2421])).

tff(c_2974,plain,(
    ! [A_226,B_227] :
      ( k1_partfun1(A_226,A_226,'#skF_2','#skF_2',k2_funct_2(A_226,B_227),'#skF_3') = k5_relat_1(k2_funct_2(A_226,B_227),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_226,B_227))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ v3_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_1(B_227) ) ),
    inference(resolution,[status(thm)],[c_26,c_2438])).

tff(c_2984,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2974])).

tff(c_2998,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2268,c_2266,c_2266,c_2266,c_2984])).

tff(c_3363,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3290,c_2998])).

tff(c_246,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( r2_relset_1(A_72,B_73,C_74,C_74)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_272,plain,(
    ! [A_78,C_79] :
      ( r2_relset_1(A_78,A_78,C_79,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,A_78))) ) ),
    inference(resolution,[status(thm)],[c_36,c_246])).

tff(c_280,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_36,c_272])).

tff(c_71,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_176,plain,(
    ! [C_59,A_60,B_61] :
      ( v2_funct_1(C_59)
      | ~ v3_funct_2(C_59,A_60,B_61)
      | ~ v1_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_182,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_190,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_182])).

tff(c_301,plain,(
    ! [A_88,B_89] :
      ( k2_funct_2(A_88,B_89) = k2_funct_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v3_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_307,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_301])).

tff(c_315,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_307])).

tff(c_417,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k2_funct_2(A_102,B_103),k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_450,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_417])).

tff(c_465,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_450])).

tff(c_519,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_14])).

tff(c_256,plain,(
    ! [A_76,B_77] :
      ( v1_funct_1(k2_funct_2(A_76,B_77))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_zfmisc_1(A_76,A_76)))
      | ~ v3_funct_2(B_77,A_76,A_76)
      | ~ v1_funct_2(B_77,A_76,A_76)
      | ~ v1_funct_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_262,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_256])).

tff(c_270,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_262])).

tff(c_317,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_270])).

tff(c_340,plain,(
    ! [A_98,B_99] :
      ( v3_funct_2(k2_funct_2(A_98,B_99),A_98,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v3_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_344,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_340])).

tff(c_351,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_315,c_344])).

tff(c_486,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_22])).

tff(c_517,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_351,c_486])).

tff(c_323,plain,(
    ! [A_90,B_91] :
      ( v1_funct_2(k2_funct_2(A_90,B_91),A_90,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_90,A_90)))
      | ~ v3_funct_2(B_91,A_90,A_90)
      | ~ v1_funct_2(B_91,A_90,A_90)
      | ~ v1_funct_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_327,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_323])).

tff(c_334,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_315,c_327])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( k2_funct_2(A_32,B_33) = k2_funct_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v3_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_472,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_40])).

tff(c_504,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_334,c_351,c_472])).

tff(c_4,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_447,plain,(
    ! [A_102,B_103] :
      ( v1_relat_1(k2_funct_2(A_102,B_103))
      | ~ v1_relat_1(k2_zfmisc_1(A_102,A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_417,c_4])).

tff(c_612,plain,(
    ! [A_113,B_114] :
      ( v1_relat_1(k2_funct_2(A_113,B_114))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(A_113,A_113)))
      | ~ v3_funct_2(B_114,A_113,A_113)
      | ~ v1_funct_2(B_114,A_113,A_113)
      | ~ v1_funct_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_447])).

tff(c_615,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_612])).

tff(c_631,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_334,c_351,c_504,c_615])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( v1_funct_1(k2_funct_2(A_23,B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_477,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_32])).

tff(c_508,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_334,c_351,c_477])).

tff(c_575,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_508])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( v3_funct_2(k2_funct_2(A_23,B_24),A_23,A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_467,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_28])).

tff(c_498,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_334,c_351,c_467])).

tff(c_590,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_498])).

tff(c_579,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_26])).

tff(c_583,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_334,c_351,c_465,c_579])).

tff(c_742,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_583,c_22])).

tff(c_785,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_590,c_742])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( v1_funct_2(k2_funct_2(A_23,B_24),A_23,A_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_469,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_465,c_30])).

tff(c_501,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_334,c_351,c_469])).

tff(c_596,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_501])).

tff(c_736,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_583,c_44])).

tff(c_779,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_596,c_736])).

tff(c_786,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_583,c_16])).

tff(c_1231,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_786])).

tff(c_728,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_583,c_40])).

tff(c_772,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_596,c_590,c_728])).

tff(c_935,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_772])).

tff(c_941,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_54,c_190,c_315,c_935])).

tff(c_8,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_152,plain,(
    ! [A_57] :
      ( k5_relat_1(k2_funct_1(A_57),A_57) = k6_partfun1(k2_relat_1(A_57))
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_161,plain,(
    ! [A_9] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_9))) = k5_relat_1(A_9,k2_funct_1(A_9))
      | ~ v2_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(k2_funct_1(A_9))
      | ~ v1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_971,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_161])).

tff(c_996,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_575,c_785,c_519,c_941,c_317,c_941,c_517,c_941,c_941,c_971])).

tff(c_164,plain,(
    ! [A_58] :
      ( k5_relat_1(A_58,k2_funct_1(A_58)) = k6_partfun1(k1_relat_1(A_58))
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_173,plain,(
    ! [A_9] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_9))) = k5_relat_1(k2_funct_1(A_9),A_9)
      | ~ v2_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(k2_funct_1(A_9))
      | ~ v1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_164])).

tff(c_1250,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_173])).

tff(c_1266,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_317,c_517,c_631,c_575,c_785,c_1231,c_1250])).

tff(c_1284,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_161])).

tff(c_1331,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_54,c_190,c_519,c_317,c_517,c_1284])).

tff(c_524,plain,(
    ! [D_104,C_108,A_106,F_107,B_105,E_109] :
      ( k1_partfun1(A_106,B_105,C_108,D_104,E_109,F_107) = k5_relat_1(E_109,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_108,D_104)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_526,plain,(
    ! [A_106,B_105,E_109] :
      ( k1_partfun1(A_106,B_105,'#skF_2','#skF_2',E_109,k2_funct_1('#skF_3')) = k5_relat_1(E_109,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_465,c_524])).

tff(c_1961,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_2',E_142,k2_funct_1('#skF_3')) = k5_relat_1(E_142,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_526])).

tff(c_1991,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1961])).

tff(c_2011,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1331,c_1991])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_318,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_70])).

tff(c_2014,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_318])).

tff(c_2017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_2014])).

tff(c_2018,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2269,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_2018])).

tff(c_3364,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3363,c_2269])).

tff(c_3367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_3364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:28:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.33/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.05  
% 5.33/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.33/2.06  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.33/2.06  
% 5.33/2.06  %Foreground sorts:
% 5.33/2.06  
% 5.33/2.06  
% 5.33/2.06  %Background operators:
% 5.33/2.06  
% 5.33/2.06  
% 5.33/2.06  %Foreground operators:
% 5.33/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.33/2.06  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.33/2.06  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.33/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.06  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.33/2.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.33/2.06  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.33/2.06  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.33/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.06  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.33/2.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.33/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.06  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.33/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.06  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.33/2.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.33/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.33/2.06  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.33/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.33/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.33/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.06  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.33/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.33/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.33/2.06  
% 5.73/2.08  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.73/2.08  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.73/2.08  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.73/2.08  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.73/2.08  tff(f_144, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.73/2.08  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.73/2.08  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.73/2.08  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.73/2.08  tff(f_97, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.73/2.08  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.73/2.08  tff(f_131, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.73/2.08  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.73/2.08  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.73/2.08  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.73/2.08  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.73/2.08  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.73/2.08  tff(c_36, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.73/2.08  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.73/2.08  tff(c_2168, plain, (![A_174, B_175, C_176, D_177]: (r2_relset_1(A_174, B_175, C_176, C_176) | ~m1_subset_1(D_177, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.73/2.08  tff(c_2190, plain, (![A_179, B_180, C_181]: (r2_relset_1(A_179, B_180, C_181, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(resolution, [status(thm)], [c_2, c_2168])).
% 5.73/2.08  tff(c_2198, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_36, c_2190])).
% 5.73/2.08  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.73/2.08  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.73/2.08  tff(c_2020, plain, (![B_148, A_149]: (v1_relat_1(B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_149)) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.73/2.08  tff(c_2026, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_2020])).
% 5.73/2.08  tff(c_2036, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2026])).
% 5.73/2.08  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.73/2.08  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.73/2.08  tff(c_2125, plain, (![C_164, A_165, B_166]: (v2_funct_1(C_164) | ~v3_funct_2(C_164, A_165, B_166) | ~v1_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.73/2.08  tff(c_2131, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2125])).
% 5.73/2.08  tff(c_2139, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2131])).
% 5.73/2.08  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.73/2.08  tff(c_2252, plain, (![A_193, B_194]: (k2_funct_2(A_193, B_194)=k2_funct_1(B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.73/2.08  tff(c_2258, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2252])).
% 5.73/2.08  tff(c_2266, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2258])).
% 5.73/2.08  tff(c_2306, plain, (![A_205, B_206]: (m1_subset_1(k2_funct_2(A_205, B_206), k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_2339, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2266, c_2306])).
% 5.73/2.08  tff(c_2354, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_2339])).
% 5.73/2.08  tff(c_14, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.73/2.08  tff(c_2408, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2354, c_14])).
% 5.73/2.08  tff(c_2234, plain, (![A_188, B_189]: (v1_funct_1(k2_funct_2(A_188, B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_189, A_188, A_188) | ~v1_funct_2(B_189, A_188, A_188) | ~v1_funct_1(B_189))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_2240, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2234])).
% 5.73/2.08  tff(c_2248, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2240])).
% 5.73/2.08  tff(c_2268, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_2248])).
% 5.73/2.08  tff(c_2291, plain, (![A_201, B_202]: (v3_funct_2(k2_funct_2(A_201, B_202), A_201, A_201) | ~m1_subset_1(B_202, k1_zfmisc_1(k2_zfmisc_1(A_201, A_201))) | ~v3_funct_2(B_202, A_201, A_201) | ~v1_funct_2(B_202, A_201, A_201) | ~v1_funct_1(B_202))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_2295, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2291])).
% 5.73/2.08  tff(c_2302, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2266, c_2295])).
% 5.73/2.08  tff(c_22, plain, (![C_22, A_20, B_21]: (v2_funct_1(C_22) | ~v3_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.73/2.08  tff(c_2375, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2354, c_22])).
% 5.73/2.08  tff(c_2406, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2268, c_2302, c_2375])).
% 5.73/2.08  tff(c_2278, plain, (![A_199, B_200]: (v1_funct_2(k2_funct_2(A_199, B_200), A_199, A_199) | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(A_199, A_199))) | ~v3_funct_2(B_200, A_199, A_199) | ~v1_funct_2(B_200, A_199, A_199) | ~v1_funct_1(B_200))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_2282, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2278])).
% 5.73/2.08  tff(c_2289, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2266, c_2282])).
% 5.73/2.08  tff(c_44, plain, (![A_35, B_36]: (k1_relset_1(A_35, A_35, B_36)=A_35 | ~m1_subset_1(B_36, k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))) | ~v1_funct_2(B_36, A_35, A_35) | ~v1_funct_1(B_36))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.73/2.08  tff(c_2367, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2354, c_44])).
% 5.73/2.08  tff(c_2399, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2268, c_2289, c_2367])).
% 5.73/2.08  tff(c_16, plain, (![A_13, B_14, C_15]: (k1_relset_1(A_13, B_14, C_15)=k1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.73/2.08  tff(c_2407, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2354, c_16])).
% 5.73/2.08  tff(c_2491, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2399, c_2407])).
% 5.73/2.08  tff(c_12, plain, (![A_9]: (k2_funct_1(k2_funct_1(A_9))=A_9 | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.73/2.08  tff(c_42, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.73/2.08  tff(c_10, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.73/2.08  tff(c_2113, plain, (![A_163]: (k5_relat_1(A_163, k2_funct_1(A_163))=k6_partfun1(k1_relat_1(A_163)) | ~v2_funct_1(A_163) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 5.73/2.08  tff(c_3204, plain, (![A_228]: (k6_partfun1(k1_relat_1(k2_funct_1(A_228)))=k5_relat_1(k2_funct_1(A_228), A_228) | ~v2_funct_1(k2_funct_1(A_228)) | ~v1_funct_1(k2_funct_1(A_228)) | ~v1_relat_1(k2_funct_1(A_228)) | ~v2_funct_1(A_228) | ~v1_funct_1(A_228) | ~v1_relat_1(A_228))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2113])).
% 5.73/2.08  tff(c_3272, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2491, c_3204])).
% 5.73/2.08  tff(c_3290, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2036, c_54, c_2139, c_2408, c_2268, c_2406, c_3272])).
% 5.73/2.08  tff(c_26, plain, (![A_23, B_24]: (m1_subset_1(k2_funct_2(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_2413, plain, (![B_208, C_211, A_209, F_210, E_212, D_207]: (k1_partfun1(A_209, B_208, C_211, D_207, E_212, F_210)=k5_relat_1(E_212, F_210) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(C_211, D_207))) | ~v1_funct_1(F_210) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))) | ~v1_funct_1(E_212))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.73/2.08  tff(c_2421, plain, (![A_209, B_208, E_212]: (k1_partfun1(A_209, B_208, '#skF_2', '#skF_2', E_212, '#skF_3')=k5_relat_1(E_212, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))) | ~v1_funct_1(E_212))), inference(resolution, [status(thm)], [c_48, c_2413])).
% 5.73/2.08  tff(c_2438, plain, (![A_213, B_214, E_215]: (k1_partfun1(A_213, B_214, '#skF_2', '#skF_2', E_215, '#skF_3')=k5_relat_1(E_215, '#skF_3') | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_1(E_215))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2421])).
% 5.73/2.08  tff(c_2974, plain, (![A_226, B_227]: (k1_partfun1(A_226, A_226, '#skF_2', '#skF_2', k2_funct_2(A_226, B_227), '#skF_3')=k5_relat_1(k2_funct_2(A_226, B_227), '#skF_3') | ~v1_funct_1(k2_funct_2(A_226, B_227)) | ~m1_subset_1(B_227, k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~v3_funct_2(B_227, A_226, A_226) | ~v1_funct_2(B_227, A_226, A_226) | ~v1_funct_1(B_227))), inference(resolution, [status(thm)], [c_26, c_2438])).
% 5.73/2.08  tff(c_2984, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2974])).
% 5.73/2.08  tff(c_2998, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2268, c_2266, c_2266, c_2266, c_2984])).
% 5.73/2.08  tff(c_3363, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3290, c_2998])).
% 5.73/2.08  tff(c_246, plain, (![A_72, B_73, C_74, D_75]: (r2_relset_1(A_72, B_73, C_74, C_74) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.73/2.08  tff(c_272, plain, (![A_78, C_79]: (r2_relset_1(A_78, A_78, C_79, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, A_78))))), inference(resolution, [status(thm)], [c_36, c_246])).
% 5.73/2.08  tff(c_280, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_36, c_272])).
% 5.73/2.08  tff(c_71, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.73/2.08  tff(c_77, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 5.73/2.08  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 5.73/2.08  tff(c_176, plain, (![C_59, A_60, B_61]: (v2_funct_1(C_59) | ~v3_funct_2(C_59, A_60, B_61) | ~v1_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.73/2.08  tff(c_182, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_176])).
% 5.73/2.08  tff(c_190, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_182])).
% 5.73/2.08  tff(c_301, plain, (![A_88, B_89]: (k2_funct_2(A_88, B_89)=k2_funct_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v3_funct_2(B_89, A_88, A_88) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.73/2.08  tff(c_307, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_301])).
% 5.73/2.08  tff(c_315, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_307])).
% 5.73/2.08  tff(c_417, plain, (![A_102, B_103]: (m1_subset_1(k2_funct_2(A_102, B_103), k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_450, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_315, c_417])).
% 5.73/2.08  tff(c_465, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_450])).
% 5.73/2.08  tff(c_519, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_14])).
% 5.73/2.08  tff(c_256, plain, (![A_76, B_77]: (v1_funct_1(k2_funct_2(A_76, B_77)) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))) | ~v3_funct_2(B_77, A_76, A_76) | ~v1_funct_2(B_77, A_76, A_76) | ~v1_funct_1(B_77))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_262, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_256])).
% 5.73/2.08  tff(c_270, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_262])).
% 5.73/2.08  tff(c_317, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_270])).
% 5.73/2.08  tff(c_340, plain, (![A_98, B_99]: (v3_funct_2(k2_funct_2(A_98, B_99), A_98, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v3_funct_2(B_99, A_98, A_98) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_344, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_340])).
% 5.73/2.08  tff(c_351, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_315, c_344])).
% 5.73/2.08  tff(c_486, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_22])).
% 5.73/2.08  tff(c_517, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_351, c_486])).
% 5.73/2.08  tff(c_323, plain, (![A_90, B_91]: (v1_funct_2(k2_funct_2(A_90, B_91), A_90, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(A_90, A_90))) | ~v3_funct_2(B_91, A_90, A_90) | ~v1_funct_2(B_91, A_90, A_90) | ~v1_funct_1(B_91))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_327, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_323])).
% 5.73/2.08  tff(c_334, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_315, c_327])).
% 5.73/2.08  tff(c_40, plain, (![A_32, B_33]: (k2_funct_2(A_32, B_33)=k2_funct_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v3_funct_2(B_33, A_32, A_32) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.73/2.08  tff(c_472, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_40])).
% 5.73/2.08  tff(c_504, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_334, c_351, c_472])).
% 5.73/2.08  tff(c_4, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.73/2.08  tff(c_447, plain, (![A_102, B_103]: (v1_relat_1(k2_funct_2(A_102, B_103)) | ~v1_relat_1(k2_zfmisc_1(A_102, A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(resolution, [status(thm)], [c_417, c_4])).
% 5.73/2.08  tff(c_612, plain, (![A_113, B_114]: (v1_relat_1(k2_funct_2(A_113, B_114)) | ~m1_subset_1(B_114, k1_zfmisc_1(k2_zfmisc_1(A_113, A_113))) | ~v3_funct_2(B_114, A_113, A_113) | ~v1_funct_2(B_114, A_113, A_113) | ~v1_funct_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_447])).
% 5.73/2.08  tff(c_615, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_612])).
% 5.73/2.08  tff(c_631, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_334, c_351, c_504, c_615])).
% 5.73/2.08  tff(c_32, plain, (![A_23, B_24]: (v1_funct_1(k2_funct_2(A_23, B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_477, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_32])).
% 5.73/2.08  tff(c_508, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_334, c_351, c_477])).
% 5.73/2.08  tff(c_575, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_508])).
% 5.73/2.08  tff(c_28, plain, (![A_23, B_24]: (v3_funct_2(k2_funct_2(A_23, B_24), A_23, A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_467, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_28])).
% 5.73/2.08  tff(c_498, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_334, c_351, c_467])).
% 5.73/2.08  tff(c_590, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_498])).
% 5.73/2.08  tff(c_579, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_504, c_26])).
% 5.73/2.08  tff(c_583, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_334, c_351, c_465, c_579])).
% 5.73/2.08  tff(c_742, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_583, c_22])).
% 5.73/2.08  tff(c_785, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_590, c_742])).
% 5.73/2.08  tff(c_30, plain, (![A_23, B_24]: (v1_funct_2(k2_funct_2(A_23, B_24), A_23, A_23) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.73/2.08  tff(c_469, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_465, c_30])).
% 5.73/2.08  tff(c_501, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_334, c_351, c_469])).
% 5.73/2.08  tff(c_596, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_501])).
% 5.73/2.08  tff(c_736, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_583, c_44])).
% 5.73/2.08  tff(c_779, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_575, c_596, c_736])).
% 5.73/2.08  tff(c_786, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_583, c_16])).
% 5.73/2.08  tff(c_1231, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_779, c_786])).
% 5.73/2.08  tff(c_728, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_583, c_40])).
% 5.73/2.08  tff(c_772, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_596, c_590, c_728])).
% 5.73/2.08  tff(c_935, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_772])).
% 5.73/2.08  tff(c_941, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_54, c_190, c_315, c_935])).
% 5.73/2.08  tff(c_8, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.73/2.08  tff(c_152, plain, (![A_57]: (k5_relat_1(k2_funct_1(A_57), A_57)=k6_partfun1(k2_relat_1(A_57)) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 5.73/2.08  tff(c_161, plain, (![A_9]: (k6_partfun1(k2_relat_1(k2_funct_1(A_9)))=k5_relat_1(A_9, k2_funct_1(A_9)) | ~v2_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(k2_funct_1(A_9)) | ~v1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_152])).
% 5.73/2.08  tff(c_971, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_941, c_161])).
% 5.73/2.08  tff(c_996, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_575, c_785, c_519, c_941, c_317, c_941, c_517, c_941, c_941, c_971])).
% 5.73/2.08  tff(c_164, plain, (![A_58]: (k5_relat_1(A_58, k2_funct_1(A_58))=k6_partfun1(k1_relat_1(A_58)) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 5.73/2.08  tff(c_173, plain, (![A_9]: (k6_partfun1(k1_relat_1(k2_funct_1(A_9)))=k5_relat_1(k2_funct_1(A_9), A_9) | ~v2_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(k2_funct_1(A_9)) | ~v1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_164])).
% 5.73/2.08  tff(c_1250, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_996, c_173])).
% 5.73/2.08  tff(c_1266, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_317, c_517, c_631, c_575, c_785, c_1231, c_1250])).
% 5.73/2.08  tff(c_1284, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_161])).
% 5.73/2.08  tff(c_1331, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_54, c_190, c_519, c_317, c_517, c_1284])).
% 5.73/2.08  tff(c_524, plain, (![D_104, C_108, A_106, F_107, B_105, E_109]: (k1_partfun1(A_106, B_105, C_108, D_104, E_109, F_107)=k5_relat_1(E_109, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_108, D_104))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.73/2.08  tff(c_526, plain, (![A_106, B_105, E_109]: (k1_partfun1(A_106, B_105, '#skF_2', '#skF_2', E_109, k2_funct_1('#skF_3'))=k5_relat_1(E_109, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_465, c_524])).
% 5.73/2.08  tff(c_1961, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_2', E_142, k2_funct_1('#skF_3'))=k5_relat_1(E_142, k2_funct_1('#skF_3')) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_526])).
% 5.73/2.08  tff(c_1991, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1961])).
% 5.73/2.08  tff(c_2011, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1331, c_1991])).
% 5.73/2.08  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.73/2.08  tff(c_70, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.73/2.08  tff(c_318, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_70])).
% 5.73/2.08  tff(c_2014, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2011, c_318])).
% 5.73/2.08  tff(c_2017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_2014])).
% 5.73/2.08  tff(c_2018, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 5.73/2.08  tff(c_2269, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_2018])).
% 5.73/2.08  tff(c_3364, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3363, c_2269])).
% 5.73/2.08  tff(c_3367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2198, c_3364])).
% 5.73/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.08  
% 5.73/2.08  Inference rules
% 5.73/2.08  ----------------------
% 5.73/2.08  #Ref     : 0
% 5.73/2.08  #Sup     : 795
% 5.73/2.08  #Fact    : 0
% 5.73/2.08  #Define  : 0
% 5.73/2.08  #Split   : 2
% 5.73/2.08  #Chain   : 0
% 5.73/2.08  #Close   : 0
% 5.73/2.08  
% 5.73/2.08  Ordering : KBO
% 5.73/2.08  
% 5.73/2.08  Simplification rules
% 5.73/2.08  ----------------------
% 5.73/2.08  #Subsume      : 84
% 5.73/2.08  #Demod        : 1455
% 5.73/2.08  #Tautology    : 335
% 5.73/2.08  #SimpNegUnit  : 0
% 5.73/2.08  #BackRed      : 33
% 5.73/2.08  
% 5.73/2.08  #Partial instantiations: 0
% 5.73/2.08  #Strategies tried      : 1
% 5.73/2.08  
% 5.73/2.08  Timing (in seconds)
% 5.73/2.08  ----------------------
% 5.73/2.09  Preprocessing        : 0.35
% 5.73/2.09  Parsing              : 0.20
% 5.73/2.09  CNF conversion       : 0.02
% 5.73/2.09  Main loop            : 0.92
% 5.73/2.09  Inferencing          : 0.30
% 5.73/2.09  Reduction            : 0.37
% 5.73/2.09  Demodulation         : 0.29
% 5.73/2.09  BG Simplification    : 0.04
% 5.73/2.09  Subsumption          : 0.14
% 5.73/2.09  Abstraction          : 0.04
% 5.73/2.09  MUC search           : 0.00
% 5.73/2.09  Cooper               : 0.00
% 5.73/2.09  Total                : 1.34
% 5.73/2.09  Index Insertion      : 0.00
% 5.73/2.09  Index Deletion       : 0.00
% 5.73/2.09  Index Matching       : 0.00
% 5.73/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
