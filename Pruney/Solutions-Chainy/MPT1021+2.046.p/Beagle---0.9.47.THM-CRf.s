%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:06 EST 2020

% Result     : Theorem 5.53s
% Output     : CNFRefutation 5.88s
% Verified   : 
% Statistics : Number of formulae       :  177 (8012 expanded)
%              Number of leaves         :   40 (3240 expanded)
%              Depth                    :   22
%              Number of atoms          :  437 (29352 expanded)
%              Number of equality atoms :   60 (1485 expanded)
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

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_151,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_104,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_38,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2144,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( r2_relset_1(A_166,B_167,C_168,C_168)
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2163,plain,(
    ! [A_170,B_171,C_172] :
      ( r2_relset_1(A_170,B_171,C_172,C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(resolution,[status(thm)],[c_2,c_2144])).

tff(c_2171,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_38,c_2163])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2195,plain,(
    ! [A_182,B_183] :
      ( k2_funct_2(A_182,B_183) = k2_funct_1(B_183)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_zfmisc_1(A_182,A_182)))
      | ~ v3_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2201,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2195])).

tff(c_2209,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2201])).

tff(c_2177,plain,(
    ! [A_177,B_178] :
      ( v1_funct_1(k2_funct_2(A_177,B_178))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(k2_zfmisc_1(A_177,A_177)))
      | ~ v3_funct_2(B_178,A_177,A_177)
      | ~ v1_funct_2(B_178,A_177,A_177)
      | ~ v1_funct_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2183,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2177])).

tff(c_2191,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2183])).

tff(c_2211,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_2191])).

tff(c_1989,plain,(
    ! [C_140,A_141,B_142] :
      ( v1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2001,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1989])).

tff(c_2083,plain,(
    ! [C_154,A_155,B_156] :
      ( v2_funct_1(C_154)
      | ~ v3_funct_2(C_154,A_155,B_156)
      | ~ v1_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2089,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2083])).

tff(c_2097,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2089])).

tff(c_2324,plain,(
    ! [A_196,B_197] :
      ( m1_subset_1(k2_funct_2(A_196,B_197),k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ v3_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2354,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2209,c_2324])).

tff(c_2366,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2354])).

tff(c_16,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2417,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2366,c_16])).

tff(c_2234,plain,(
    ! [A_189,B_190] :
      ( v3_funct_2(k2_funct_2(A_189,B_190),A_189,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2238,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2234])).

tff(c_2245,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2209,c_2238])).

tff(c_24,plain,(
    ! [C_19,A_17,B_18] :
      ( v2_funct_1(C_19)
      | ~ v3_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2387,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2366,c_24])).

tff(c_2415,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_2245,c_2387])).

tff(c_2219,plain,(
    ! [A_185,B_186] :
      ( v1_funct_2(k2_funct_2(A_185,B_186),A_185,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185)))
      | ~ v3_funct_2(B_186,A_185,A_185)
      | ~ v1_funct_2(B_186,A_185,A_185)
      | ~ v1_funct_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2223,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2219])).

tff(c_2230,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2209,c_2223])).

tff(c_46,plain,(
    ! [A_32,B_33] :
      ( k1_relset_1(A_32,A_32,B_33) = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2381,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2366,c_46])).

tff(c_2409,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_2230,c_2381])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2416,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2366,c_18])).

tff(c_2470,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2409,c_2416])).

tff(c_14,plain,(
    ! [A_6] :
      ( k2_funct_1(k2_funct_1(A_6)) = A_6
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2071,plain,(
    ! [A_153] :
      ( k5_relat_1(A_153,k2_funct_1(A_153)) = k6_partfun1(k1_relat_1(A_153))
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_2080,plain,(
    ! [A_6] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_6))) = k5_relat_1(k2_funct_1(A_6),A_6)
      | ~ v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2071])).

tff(c_2474,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2470,c_2080])).

tff(c_2478,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2001,c_56,c_2097,c_2417,c_2211,c_2415,c_2474])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2437,plain,(
    ! [F_199,A_203,E_200,C_198,D_202,B_201] :
      ( k1_partfun1(A_203,B_201,C_198,D_202,E_200,F_199) = k5_relat_1(E_200,F_199)
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_198,D_202)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2445,plain,(
    ! [A_203,B_201,E_200] :
      ( k1_partfun1(A_203,B_201,'#skF_2','#skF_2',E_200,'#skF_3') = k5_relat_1(E_200,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_50,c_2437])).

tff(c_2480,plain,(
    ! [A_204,B_205,E_206] :
      ( k1_partfun1(A_204,B_205,'#skF_2','#skF_2',E_206,'#skF_3') = k5_relat_1(E_206,'#skF_3')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(E_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2445])).

tff(c_3219,plain,(
    ! [A_221,B_222] :
      ( k1_partfun1(A_221,A_221,'#skF_2','#skF_2',k2_funct_2(A_221,B_222),'#skF_3') = k5_relat_1(k2_funct_2(A_221,B_222),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_221,B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ v3_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_1(B_222) ) ),
    inference(resolution,[status(thm)],[c_28,c_2480])).

tff(c_3231,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3219])).

tff(c_3246,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2211,c_2209,c_2478,c_2209,c_2209,c_3231])).

tff(c_202,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_relset_1(A_62,B_63,C_64,C_64)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_212,plain,(
    ! [A_66,C_67] :
      ( r2_relset_1(A_66,A_66,C_67,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,A_66))) ) ),
    inference(resolution,[status(thm)],[c_38,c_202])).

tff(c_220,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_38,c_212])).

tff(c_74,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_74])).

tff(c_168,plain,(
    ! [C_54,A_55,B_56] :
      ( v2_funct_1(C_54)
      | ~ v3_funct_2(C_54,A_55,B_56)
      | ~ v1_funct_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_174,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_168])).

tff(c_182,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_174])).

tff(c_293,plain,(
    ! [A_83,B_84] :
      ( k2_funct_2(A_83,B_84) = k2_funct_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v3_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_299,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_293])).

tff(c_307,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_299])).

tff(c_409,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k2_funct_2(A_97,B_98),k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_439,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_409])).

tff(c_451,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_439])).

tff(c_502,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_16])).

tff(c_264,plain,(
    ! [A_75,B_76] :
      ( v1_funct_1(k2_funct_2(A_75,B_76))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_zfmisc_1(A_75,A_75)))
      | ~ v3_funct_2(B_76,A_75,A_75)
      | ~ v1_funct_2(B_76,A_75,A_75)
      | ~ v1_funct_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_270,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_264])).

tff(c_278,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_270])).

tff(c_309,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_278])).

tff(c_315,plain,(
    ! [A_85,B_86] :
      ( v3_funct_2(k2_funct_2(A_85,B_86),A_85,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_319,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_315])).

tff(c_326,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_307,c_319])).

tff(c_472,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_24])).

tff(c_500,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_326,c_472])).

tff(c_332,plain,(
    ! [A_93,B_94] :
      ( v1_funct_2(k2_funct_2(A_93,B_94),A_93,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_zfmisc_1(A_93,A_93)))
      | ~ v3_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_2(B_94,A_93,A_93)
      | ~ v1_funct_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_336,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_332])).

tff(c_343,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_307,c_336])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_458,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_42])).

tff(c_487,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_458])).

tff(c_605,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(k2_funct_2(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_409,c_16])).

tff(c_608,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_605])).

tff(c_624,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_487,c_608])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k2_funct_2(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_461,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_34])).

tff(c_490,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_461])).

tff(c_528,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_490])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( v3_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_455,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_30])).

tff(c_484,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_455])).

tff(c_569,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_484])).

tff(c_532,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_487,c_28])).

tff(c_536,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_451,c_532])).

tff(c_721,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_24])).

tff(c_761,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_569,c_721])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( v1_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_453,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_451,c_32])).

tff(c_481,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_343,c_326,c_453])).

tff(c_575,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_481])).

tff(c_713,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_46])).

tff(c_754,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_575,c_713])).

tff(c_762,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_18])).

tff(c_1213,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_762])).

tff(c_707,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_536,c_42])).

tff(c_748,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_575,c_569,c_707])).

tff(c_908,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_748])).

tff(c_914,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_56,c_182,c_307,c_908])).

tff(c_8,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,(
    ! [A_52] :
      ( k5_relat_1(k2_funct_1(A_52),A_52) = k6_partfun1(k2_relat_1(A_52))
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_153,plain,(
    ! [A_6] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_6))) = k5_relat_1(A_6,k2_funct_1(A_6))
      | ~ v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_945,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_153])).

tff(c_979,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_528,c_761,c_502,c_914,c_309,c_914,c_500,c_914,c_914,c_945])).

tff(c_156,plain,(
    ! [A_53] :
      ( k5_relat_1(A_53,k2_funct_1(A_53)) = k6_partfun1(k1_relat_1(A_53))
      | ~ v2_funct_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_165,plain,(
    ! [A_6] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_6))) = k5_relat_1(k2_funct_1(A_6),A_6)
      | ~ v2_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(k2_funct_1(A_6))
      | ~ v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_1262,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_165])).

tff(c_1278,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_309,c_500,c_624,c_528,c_761,c_1213,c_1262])).

tff(c_1298,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_153])).

tff(c_1344,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_56,c_182,c_502,c_309,c_500,c_1298])).

tff(c_503,plain,(
    ! [C_99,D_103,B_102,A_104,F_100,E_101] :
      ( k1_partfun1(A_104,B_102,C_99,D_103,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_99,D_103)))
      | ~ v1_funct_1(F_100)
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_505,plain,(
    ! [A_104,B_102,E_101] :
      ( k1_partfun1(A_104,B_102,'#skF_2','#skF_2',E_101,k2_funct_1('#skF_3')) = k5_relat_1(E_101,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_1(E_101) ) ),
    inference(resolution,[status(thm)],[c_451,c_503])).

tff(c_1930,plain,(
    ! [A_136,B_137,E_138] :
      ( k1_partfun1(A_136,B_137,'#skF_2','#skF_2',E_138,k2_funct_1('#skF_3')) = k5_relat_1(E_138,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_1(E_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_505])).

tff(c_1960,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1930])).

tff(c_1980,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1344,c_1960])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_310,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_72])).

tff(c_1982,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1980,c_310])).

tff(c_1985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1982])).

tff(c_1986,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2213,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_1986])).

tff(c_3369,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3246,c_2213])).

tff(c_3372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2171,c_3369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:16:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.53/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.10  
% 5.63/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.10  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.63/2.10  
% 5.63/2.10  %Foreground sorts:
% 5.63/2.10  
% 5.63/2.10  
% 5.63/2.10  %Background operators:
% 5.63/2.10  
% 5.63/2.10  
% 5.63/2.10  %Foreground operators:
% 5.63/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.63/2.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.63/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.63/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.63/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.63/2.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.63/2.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.63/2.10  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.63/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.63/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.63/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.63/2.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.63/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.63/2.10  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.63/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.63/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.63/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.63/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.63/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.63/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.63/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.63/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.63/2.10  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.63/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.63/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.63/2.10  
% 5.88/2.14  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.88/2.14  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.88/2.14  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.88/2.14  tff(f_151, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.88/2.14  tff(f_128, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.88/2.14  tff(f_104, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.88/2.14  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.88/2.14  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.88/2.14  tff(f_138, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.88/2.14  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.88/2.14  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.88/2.14  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.88/2.14  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.88/2.14  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.88/2.14  tff(c_38, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.88/2.14  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.88/2.14  tff(c_2144, plain, (![A_166, B_167, C_168, D_169]: (r2_relset_1(A_166, B_167, C_168, C_168) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.88/2.14  tff(c_2163, plain, (![A_170, B_171, C_172]: (r2_relset_1(A_170, B_171, C_172, C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(resolution, [status(thm)], [c_2, c_2144])).
% 5.88/2.14  tff(c_2171, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_38, c_2163])).
% 5.88/2.14  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.88/2.14  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.88/2.14  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.88/2.14  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.88/2.14  tff(c_2195, plain, (![A_182, B_183]: (k2_funct_2(A_182, B_183)=k2_funct_1(B_183) | ~m1_subset_1(B_183, k1_zfmisc_1(k2_zfmisc_1(A_182, A_182))) | ~v3_funct_2(B_183, A_182, A_182) | ~v1_funct_2(B_183, A_182, A_182) | ~v1_funct_1(B_183))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.88/2.14  tff(c_2201, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2195])).
% 5.88/2.14  tff(c_2209, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2201])).
% 5.88/2.14  tff(c_2177, plain, (![A_177, B_178]: (v1_funct_1(k2_funct_2(A_177, B_178)) | ~m1_subset_1(B_178, k1_zfmisc_1(k2_zfmisc_1(A_177, A_177))) | ~v3_funct_2(B_178, A_177, A_177) | ~v1_funct_2(B_178, A_177, A_177) | ~v1_funct_1(B_178))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_2183, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2177])).
% 5.88/2.14  tff(c_2191, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2183])).
% 5.88/2.14  tff(c_2211, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_2191])).
% 5.88/2.14  tff(c_1989, plain, (![C_140, A_141, B_142]: (v1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.88/2.14  tff(c_2001, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1989])).
% 5.88/2.14  tff(c_2083, plain, (![C_154, A_155, B_156]: (v2_funct_1(C_154) | ~v3_funct_2(C_154, A_155, B_156) | ~v1_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.88/2.14  tff(c_2089, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2083])).
% 5.88/2.14  tff(c_2097, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2089])).
% 5.88/2.14  tff(c_2324, plain, (![A_196, B_197]: (m1_subset_1(k2_funct_2(A_196, B_197), k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~v3_funct_2(B_197, A_196, A_196) | ~v1_funct_2(B_197, A_196, A_196) | ~v1_funct_1(B_197))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_2354, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2209, c_2324])).
% 5.88/2.14  tff(c_2366, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2354])).
% 5.88/2.14  tff(c_16, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.88/2.14  tff(c_2417, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2366, c_16])).
% 5.88/2.14  tff(c_2234, plain, (![A_189, B_190]: (v3_funct_2(k2_funct_2(A_189, B_190), A_189, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_2238, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2234])).
% 5.88/2.14  tff(c_2245, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2209, c_2238])).
% 5.88/2.14  tff(c_24, plain, (![C_19, A_17, B_18]: (v2_funct_1(C_19) | ~v3_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.88/2.14  tff(c_2387, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2366, c_24])).
% 5.88/2.14  tff(c_2415, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_2245, c_2387])).
% 5.88/2.14  tff(c_2219, plain, (![A_185, B_186]: (v1_funct_2(k2_funct_2(A_185, B_186), A_185, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_185, A_185))) | ~v3_funct_2(B_186, A_185, A_185) | ~v1_funct_2(B_186, A_185, A_185) | ~v1_funct_1(B_186))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_2223, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2219])).
% 5.88/2.14  tff(c_2230, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2209, c_2223])).
% 5.88/2.14  tff(c_46, plain, (![A_32, B_33]: (k1_relset_1(A_32, A_32, B_33)=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.88/2.14  tff(c_2381, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2366, c_46])).
% 5.88/2.14  tff(c_2409, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_2230, c_2381])).
% 5.88/2.14  tff(c_18, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.88/2.14  tff(c_2416, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2366, c_18])).
% 5.88/2.14  tff(c_2470, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2409, c_2416])).
% 5.88/2.14  tff(c_14, plain, (![A_6]: (k2_funct_1(k2_funct_1(A_6))=A_6 | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.88/2.14  tff(c_44, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.88/2.14  tff(c_10, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.14  tff(c_2071, plain, (![A_153]: (k5_relat_1(A_153, k2_funct_1(A_153))=k6_partfun1(k1_relat_1(A_153)) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.88/2.14  tff(c_2080, plain, (![A_6]: (k6_partfun1(k1_relat_1(k2_funct_1(A_6)))=k5_relat_1(k2_funct_1(A_6), A_6) | ~v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2071])).
% 5.88/2.14  tff(c_2474, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2470, c_2080])).
% 5.88/2.14  tff(c_2478, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2001, c_56, c_2097, c_2417, c_2211, c_2415, c_2474])).
% 5.88/2.14  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_2437, plain, (![F_199, A_203, E_200, C_198, D_202, B_201]: (k1_partfun1(A_203, B_201, C_198, D_202, E_200, F_199)=k5_relat_1(E_200, F_199) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_198, D_202))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.88/2.14  tff(c_2445, plain, (![A_203, B_201, E_200]: (k1_partfun1(A_203, B_201, '#skF_2', '#skF_2', E_200, '#skF_3')=k5_relat_1(E_200, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_50, c_2437])).
% 5.88/2.14  tff(c_2480, plain, (![A_204, B_205, E_206]: (k1_partfun1(A_204, B_205, '#skF_2', '#skF_2', E_206, '#skF_3')=k5_relat_1(E_206, '#skF_3') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(E_206))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2445])).
% 5.88/2.14  tff(c_3219, plain, (![A_221, B_222]: (k1_partfun1(A_221, A_221, '#skF_2', '#skF_2', k2_funct_2(A_221, B_222), '#skF_3')=k5_relat_1(k2_funct_2(A_221, B_222), '#skF_3') | ~v1_funct_1(k2_funct_2(A_221, B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~v3_funct_2(B_222, A_221, A_221) | ~v1_funct_2(B_222, A_221, A_221) | ~v1_funct_1(B_222))), inference(resolution, [status(thm)], [c_28, c_2480])).
% 5.88/2.14  tff(c_3231, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3219])).
% 5.88/2.14  tff(c_3246, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2211, c_2209, c_2478, c_2209, c_2209, c_3231])).
% 5.88/2.14  tff(c_202, plain, (![A_62, B_63, C_64, D_65]: (r2_relset_1(A_62, B_63, C_64, C_64) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.88/2.14  tff(c_212, plain, (![A_66, C_67]: (r2_relset_1(A_66, A_66, C_67, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, A_66))))), inference(resolution, [status(thm)], [c_38, c_202])).
% 5.88/2.14  tff(c_220, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_38, c_212])).
% 5.88/2.14  tff(c_74, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.88/2.14  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_74])).
% 5.88/2.14  tff(c_168, plain, (![C_54, A_55, B_56]: (v2_funct_1(C_54) | ~v3_funct_2(C_54, A_55, B_56) | ~v1_funct_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.88/2.14  tff(c_174, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_168])).
% 5.88/2.14  tff(c_182, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_174])).
% 5.88/2.14  tff(c_293, plain, (![A_83, B_84]: (k2_funct_2(A_83, B_84)=k2_funct_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v3_funct_2(B_84, A_83, A_83) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.88/2.14  tff(c_299, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_293])).
% 5.88/2.14  tff(c_307, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_299])).
% 5.88/2.14  tff(c_409, plain, (![A_97, B_98]: (m1_subset_1(k2_funct_2(A_97, B_98), k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_439, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_307, c_409])).
% 5.88/2.14  tff(c_451, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_439])).
% 5.88/2.14  tff(c_502, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_16])).
% 5.88/2.14  tff(c_264, plain, (![A_75, B_76]: (v1_funct_1(k2_funct_2(A_75, B_76)) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_zfmisc_1(A_75, A_75))) | ~v3_funct_2(B_76, A_75, A_75) | ~v1_funct_2(B_76, A_75, A_75) | ~v1_funct_1(B_76))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_270, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_264])).
% 5.88/2.14  tff(c_278, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_270])).
% 5.88/2.14  tff(c_309, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_278])).
% 5.88/2.14  tff(c_315, plain, (![A_85, B_86]: (v3_funct_2(k2_funct_2(A_85, B_86), A_85, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_319, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_315])).
% 5.88/2.14  tff(c_326, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_307, c_319])).
% 5.88/2.14  tff(c_472, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_24])).
% 5.88/2.14  tff(c_500, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_326, c_472])).
% 5.88/2.14  tff(c_332, plain, (![A_93, B_94]: (v1_funct_2(k2_funct_2(A_93, B_94), A_93, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))) | ~v3_funct_2(B_94, A_93, A_93) | ~v1_funct_2(B_94, A_93, A_93) | ~v1_funct_1(B_94))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_336, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_332])).
% 5.88/2.14  tff(c_343, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_307, c_336])).
% 5.88/2.14  tff(c_42, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.88/2.14  tff(c_458, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_42])).
% 5.88/2.14  tff(c_487, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_458])).
% 5.88/2.14  tff(c_605, plain, (![A_108, B_109]: (v1_relat_1(k2_funct_2(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(resolution, [status(thm)], [c_409, c_16])).
% 5.88/2.14  tff(c_608, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_605])).
% 5.88/2.14  tff(c_624, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_487, c_608])).
% 5.88/2.14  tff(c_34, plain, (![A_20, B_21]: (v1_funct_1(k2_funct_2(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_461, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_34])).
% 5.88/2.14  tff(c_490, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_461])).
% 5.88/2.14  tff(c_528, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_490])).
% 5.88/2.14  tff(c_30, plain, (![A_20, B_21]: (v3_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_455, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_30])).
% 5.88/2.14  tff(c_484, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_455])).
% 5.88/2.14  tff(c_569, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_484])).
% 5.88/2.14  tff(c_532, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_487, c_28])).
% 5.88/2.14  tff(c_536, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_451, c_532])).
% 5.88/2.14  tff(c_721, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_24])).
% 5.88/2.14  tff(c_761, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_569, c_721])).
% 5.88/2.14  tff(c_32, plain, (![A_20, B_21]: (v1_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.88/2.14  tff(c_453, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_451, c_32])).
% 5.88/2.14  tff(c_481, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_343, c_326, c_453])).
% 5.88/2.14  tff(c_575, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_481])).
% 5.88/2.14  tff(c_713, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_46])).
% 5.88/2.14  tff(c_754, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_528, c_575, c_713])).
% 5.88/2.14  tff(c_762, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_18])).
% 5.88/2.14  tff(c_1213, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_754, c_762])).
% 5.88/2.14  tff(c_707, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_536, c_42])).
% 5.88/2.14  tff(c_748, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_528, c_575, c_569, c_707])).
% 5.88/2.14  tff(c_908, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_748])).
% 5.88/2.14  tff(c_914, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_56, c_182, c_307, c_908])).
% 5.88/2.14  tff(c_8, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.88/2.14  tff(c_144, plain, (![A_52]: (k5_relat_1(k2_funct_1(A_52), A_52)=k6_partfun1(k2_relat_1(A_52)) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 5.88/2.14  tff(c_153, plain, (![A_6]: (k6_partfun1(k2_relat_1(k2_funct_1(A_6)))=k5_relat_1(A_6, k2_funct_1(A_6)) | ~v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 5.88/2.14  tff(c_945, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_914, c_153])).
% 5.88/2.14  tff(c_979, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_528, c_761, c_502, c_914, c_309, c_914, c_500, c_914, c_914, c_945])).
% 5.88/2.14  tff(c_156, plain, (![A_53]: (k5_relat_1(A_53, k2_funct_1(A_53))=k6_partfun1(k1_relat_1(A_53)) | ~v2_funct_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.88/2.14  tff(c_165, plain, (![A_6]: (k6_partfun1(k1_relat_1(k2_funct_1(A_6)))=k5_relat_1(k2_funct_1(A_6), A_6) | ~v2_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(k2_funct_1(A_6)) | ~v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 5.88/2.14  tff(c_1262, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_979, c_165])).
% 5.88/2.14  tff(c_1278, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_502, c_309, c_500, c_624, c_528, c_761, c_1213, c_1262])).
% 5.88/2.14  tff(c_1298, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1278, c_153])).
% 5.88/2.14  tff(c_1344, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_56, c_182, c_502, c_309, c_500, c_1298])).
% 5.88/2.14  tff(c_503, plain, (![C_99, D_103, B_102, A_104, F_100, E_101]: (k1_partfun1(A_104, B_102, C_99, D_103, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_99, D_103))) | ~v1_funct_1(F_100) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.88/2.14  tff(c_505, plain, (![A_104, B_102, E_101]: (k1_partfun1(A_104, B_102, '#skF_2', '#skF_2', E_101, k2_funct_1('#skF_3'))=k5_relat_1(E_101, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_1(E_101))), inference(resolution, [status(thm)], [c_451, c_503])).
% 5.88/2.14  tff(c_1930, plain, (![A_136, B_137, E_138]: (k1_partfun1(A_136, B_137, '#skF_2', '#skF_2', E_138, k2_funct_1('#skF_3'))=k5_relat_1(E_138, k2_funct_1('#skF_3')) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_1(E_138))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_505])).
% 5.88/2.14  tff(c_1960, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1930])).
% 5.88/2.14  tff(c_1980, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1344, c_1960])).
% 5.88/2.14  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.88/2.14  tff(c_72, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.88/2.14  tff(c_310, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_72])).
% 5.88/2.14  tff(c_1982, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1980, c_310])).
% 5.88/2.14  tff(c_1985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_1982])).
% 5.88/2.14  tff(c_1986, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 5.88/2.14  tff(c_2213, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_1986])).
% 5.88/2.14  tff(c_3369, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3246, c_2213])).
% 5.88/2.14  tff(c_3372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2171, c_3369])).
% 5.88/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.88/2.14  
% 5.88/2.14  Inference rules
% 5.88/2.14  ----------------------
% 5.88/2.14  #Ref     : 0
% 5.88/2.14  #Sup     : 803
% 5.88/2.14  #Fact    : 0
% 5.88/2.14  #Define  : 0
% 5.88/2.14  #Split   : 3
% 5.88/2.14  #Chain   : 0
% 5.88/2.14  #Close   : 0
% 5.88/2.14  
% 5.88/2.14  Ordering : KBO
% 5.88/2.14  
% 5.88/2.14  Simplification rules
% 5.88/2.14  ----------------------
% 5.88/2.14  #Subsume      : 91
% 5.88/2.14  #Demod        : 1505
% 5.88/2.14  #Tautology    : 343
% 5.88/2.14  #SimpNegUnit  : 0
% 5.88/2.14  #BackRed      : 29
% 5.88/2.14  
% 5.88/2.14  #Partial instantiations: 0
% 5.88/2.14  #Strategies tried      : 1
% 5.88/2.14  
% 5.88/2.14  Timing (in seconds)
% 5.88/2.14  ----------------------
% 5.88/2.14  Preprocessing        : 0.36
% 5.88/2.14  Parsing              : 0.20
% 5.88/2.14  CNF conversion       : 0.02
% 5.88/2.14  Main loop            : 0.93
% 5.88/2.14  Inferencing          : 0.30
% 5.88/2.14  Reduction            : 0.37
% 5.88/2.14  Demodulation         : 0.29
% 5.88/2.14  BG Simplification    : 0.04
% 5.88/2.14  Subsumption          : 0.15
% 5.88/2.14  Abstraction          : 0.04
% 5.88/2.14  MUC search           : 0.00
% 5.88/2.14  Cooper               : 0.00
% 5.88/2.14  Total                : 1.36
% 5.88/2.14  Index Insertion      : 0.00
% 5.88/2.14  Index Deletion       : 0.00
% 5.88/2.14  Index Matching       : 0.00
% 5.88/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
