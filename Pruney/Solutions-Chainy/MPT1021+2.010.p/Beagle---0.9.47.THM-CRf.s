%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:00 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  182 (8038 expanded)
%              Number of leaves         :   41 (3248 expanded)
%              Depth                    :   22
%              Number of atoms          :  457 (29402 expanded)
%              Number of equality atoms :   61 (1491 expanded)
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

tff(f_129,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_79,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_28,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_150,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_42,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_22,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_55,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_22])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2173,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( r2_relset_1(A_170,B_171,C_172,C_172)
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2187,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_relset_1(A_174,B_175,C_176,C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(resolution,[status(thm)],[c_2,c_2173])).

tff(c_2195,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_55,c_2187])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2217,plain,(
    ! [A_183,B_184] :
      ( k2_funct_2(A_183,B_184) = k2_funct_1(B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_2(B_184,A_183,A_183)
      | ~ v1_funct_1(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2223,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2217])).

tff(c_2231,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2223])).

tff(c_2201,plain,(
    ! [A_181,B_182] :
      ( v1_funct_1(k2_funct_2(A_181,B_182))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_zfmisc_1(A_181,A_181)))
      | ~ v3_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2207,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2201])).

tff(c_2215,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2207])).

tff(c_2233,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_2215])).

tff(c_70,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_2107,plain,(
    ! [C_158,A_159,B_160] :
      ( v2_funct_1(C_158)
      | ~ v3_funct_2(C_158,A_159,B_160)
      | ~ v1_funct_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2113,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2107])).

tff(c_2121,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2113])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2405,plain,(
    ! [A_201,B_202] :
      ( m1_subset_1(k2_funct_2(A_201,B_202),k1_zfmisc_1(k2_zfmisc_1(A_201,A_201)))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(k2_zfmisc_1(A_201,A_201)))
      | ~ v3_funct_2(B_202,A_201,A_201)
      | ~ v1_funct_2(B_202,A_201,A_201)
      | ~ v1_funct_1(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2438,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2231,c_2405])).

tff(c_2453,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_2438])).

tff(c_4,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2480,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2453,c_4])).

tff(c_2509,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2480])).

tff(c_2259,plain,(
    ! [A_195,B_196] :
      ( v3_funct_2(k2_funct_2(A_195,B_196),A_195,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2263,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2259])).

tff(c_2270,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2231,c_2263])).

tff(c_26,plain,(
    ! [C_24,A_22,B_23] :
      ( v2_funct_1(C_24)
      | ~ v3_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2474,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2453,c_26])).

tff(c_2505,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2233,c_2270,c_2474])).

tff(c_2244,plain,(
    ! [A_191,B_192] :
      ( v1_funct_2(k2_funct_2(A_191,B_192),A_191,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191)))
      | ~ v3_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2248,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2244])).

tff(c_2255,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2231,c_2248])).

tff(c_44,plain,(
    ! [A_36,B_37] :
      ( k1_relset_1(A_36,A_36,B_37) = A_36
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k2_zfmisc_1(A_36,A_36)))
      | ~ v1_funct_2(B_37,A_36,A_36)
      | ~ v1_funct_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2468,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2453,c_44])).

tff(c_2499,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2233,c_2255,c_2468])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( k1_relset_1(A_14,B_15,C_16) = k1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2506,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2453,c_18])).

tff(c_2590,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_2506])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_funct_1(k2_funct_1(A_10)) = A_10
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2083,plain,(
    ! [A_156] :
      ( k5_relat_1(A_156,k2_funct_1(A_156)) = k6_partfun1(k1_relat_1(A_156))
      | ~ v2_funct_1(A_156)
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_2092,plain,(
    ! [A_10] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_10))) = k5_relat_1(k2_funct_1(A_10),A_10)
      | ~ v2_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2083])).

tff(c_2594,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2590,c_2092])).

tff(c_2598,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_54,c_2121,c_2509,c_2233,c_2505,c_2594])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_funct_2(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ v3_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2531,plain,(
    ! [D_205,F_203,E_206,C_204,A_208,B_207] :
      ( k1_partfun1(A_208,B_207,C_204,D_205,E_206,F_203) = k5_relat_1(E_206,F_203)
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(C_204,D_205)))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_1(E_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2539,plain,(
    ! [A_208,B_207,E_206] :
      ( k1_partfun1(A_208,B_207,'#skF_2','#skF_2',E_206,'#skF_3') = k5_relat_1(E_206,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_1(E_206) ) ),
    inference(resolution,[status(thm)],[c_48,c_2531])).

tff(c_2564,plain,(
    ! [A_209,B_210,E_211] :
      ( k1_partfun1(A_209,B_210,'#skF_2','#skF_2',E_211,'#skF_3') = k5_relat_1(E_211,'#skF_3')
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_1(E_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2539])).

tff(c_3123,plain,(
    ! [A_223,B_224] :
      ( k1_partfun1(A_223,A_223,'#skF_2','#skF_2',k2_funct_2(A_223,B_224),'#skF_3') = k5_relat_1(k2_funct_2(A_223,B_224),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_223,B_224))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_zfmisc_1(A_223,A_223)))
      | ~ v3_funct_2(B_224,A_223,A_223)
      | ~ v1_funct_2(B_224,A_223,A_223)
      | ~ v1_funct_1(B_224) ) ),
    inference(resolution,[status(thm)],[c_30,c_2564])).

tff(c_3133,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_3123])).

tff(c_3147,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2233,c_2231,c_2598,c_2231,c_2231,c_3133])).

tff(c_212,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( r2_relset_1(A_68,B_69,C_70,C_70)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_222,plain,(
    ! [A_72,C_73] :
      ( r2_relset_1(A_72,A_72,C_73,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,A_72))) ) ),
    inference(resolution,[status(thm)],[c_55,c_212])).

tff(c_230,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_55,c_222])).

tff(c_178,plain,(
    ! [C_60,A_61,B_62] :
      ( v2_funct_1(C_60)
      | ~ v3_funct_2(C_60,A_61,B_62)
      | ~ v1_funct_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_184,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_178])).

tff(c_192,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_184])).

tff(c_303,plain,(
    ! [A_89,B_90] :
      ( k2_funct_2(A_89,B_90) = k2_funct_1(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v3_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_309,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_303])).

tff(c_317,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_309])).

tff(c_416,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k2_funct_2(A_103,B_104),k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v3_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_449,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_416])).

tff(c_464,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_449])).

tff(c_491,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_464,c_4])).

tff(c_520,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_491])).

tff(c_274,plain,(
    ! [A_81,B_82] :
      ( v1_funct_1(k2_funct_2(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_zfmisc_1(A_81,A_81)))
      | ~ v3_funct_2(B_82,A_81,A_81)
      | ~ v1_funct_2(B_82,A_81,A_81)
      | ~ v1_funct_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_280,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_274])).

tff(c_288,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_280])).

tff(c_319,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_288])).

tff(c_342,plain,(
    ! [A_99,B_100] :
      ( v3_funct_2(k2_funct_2(A_99,B_100),A_99,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_346,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_342])).

tff(c_353,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_317,c_346])).

tff(c_485,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_464,c_26])).

tff(c_516,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_353,c_485])).

tff(c_325,plain,(
    ! [A_91,B_92] :
      ( v1_funct_2(k2_funct_2(A_91,B_92),A_91,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_329,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_325])).

tff(c_336,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_317,c_329])).

tff(c_40,plain,(
    ! [A_33,B_34] :
      ( k2_funct_2(A_33,B_34) = k2_funct_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v3_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_471,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_464,c_40])).

tff(c_503,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_336,c_353,c_471])).

tff(c_443,plain,(
    ! [A_103,B_104] :
      ( v1_relat_1(k2_funct_2(A_103,B_104))
      | ~ v1_relat_1(k2_zfmisc_1(A_103,A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v3_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_416,c_4])).

tff(c_611,plain,(
    ! [A_114,B_115] :
      ( v1_relat_1(k2_funct_2(A_114,B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_zfmisc_1(A_114,A_114)))
      | ~ v3_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_2(B_115,A_114,A_114)
      | ~ v1_funct_1(B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_443])).

tff(c_614,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_464,c_611])).

tff(c_630,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_336,c_353,c_503,c_614])).

tff(c_36,plain,(
    ! [A_25,B_26] :
      ( v1_funct_1(k2_funct_2(A_25,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ v3_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_474,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_464,c_36])).

tff(c_506,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_336,c_353,c_474])).

tff(c_574,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_506])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( v3_funct_2(k2_funct_2(A_25,B_26),A_25,A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ v3_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_466,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_464,c_32])).

tff(c_497,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_336,c_353,c_466])).

tff(c_589,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_497])).

tff(c_578,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_30])).

tff(c_582,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_336,c_353,c_464,c_578])).

tff(c_738,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_582,c_26])).

tff(c_781,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_589,c_738])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( v1_funct_2(k2_funct_2(A_25,B_26),A_25,A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ v3_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_468,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_464,c_34])).

tff(c_500,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_336,c_353,c_468])).

tff(c_595,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_500])).

tff(c_730,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_582,c_44])).

tff(c_774,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_595,c_730])).

tff(c_782,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_582,c_18])).

tff(c_1049,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_782])).

tff(c_724,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_582,c_40])).

tff(c_768,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_595,c_589,c_724])).

tff(c_866,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_768])).

tff(c_872,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_54,c_192,c_317,c_866])).

tff(c_8,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_154,plain,(
    ! [A_58] :
      ( k5_relat_1(k2_funct_1(A_58),A_58) = k6_partfun1(k2_relat_1(A_58))
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_1064,plain,(
    ! [A_124] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_124))) = k5_relat_1(A_124,k2_funct_1(A_124))
      | ~ v2_funct_1(k2_funct_1(A_124))
      | ~ v1_funct_1(k2_funct_1(A_124))
      | ~ v1_relat_1(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_154])).

tff(c_1126,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_1064])).

tff(c_1142,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_574,c_781,c_520,c_872,c_319,c_872,c_516,c_872,c_872,c_1126])).

tff(c_166,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k2_funct_1(A_59)) = k6_partfun1(k1_relat_1(A_59))
      | ~ v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_175,plain,(
    ! [A_10] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_10))) = k5_relat_1(k2_funct_1(A_10),A_10)
      | ~ v2_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_1207,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_175])).

tff(c_1223,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_319,c_516,c_630,c_574,c_781,c_1049,c_1207])).

tff(c_163,plain,(
    ! [A_10] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_10))) = k5_relat_1(A_10,k2_funct_1(A_10))
      | ~ v2_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_154])).

tff(c_1268,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1223,c_163])).

tff(c_1313,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_54,c_192,c_520,c_319,c_516,c_1268])).

tff(c_523,plain,(
    ! [E_108,A_110,F_105,D_107,B_109,C_106] :
      ( k1_partfun1(A_110,B_109,C_106,D_107,E_108,F_105) = k5_relat_1(E_108,F_105)
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_106,D_107)))
      | ~ v1_funct_1(F_105)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_1(E_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_525,plain,(
    ! [A_110,B_109,E_108] :
      ( k1_partfun1(A_110,B_109,'#skF_2','#skF_2',E_108,k2_funct_1('#skF_3')) = k5_relat_1(E_108,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109)))
      | ~ v1_funct_1(E_108) ) ),
    inference(resolution,[status(thm)],[c_464,c_523])).

tff(c_1956,plain,(
    ! [A_141,B_142,E_143] :
      ( k1_partfun1(A_141,B_142,'#skF_2','#skF_2',E_143,k2_funct_1('#skF_3')) = k5_relat_1(E_143,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_525])).

tff(c_1986,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1956])).

tff(c_2006,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1313,c_1986])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_320,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_84])).

tff(c_2008,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2006,c_320])).

tff(c_2011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_2008])).

tff(c_2012,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2235,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_2012])).

tff(c_3213,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_2235])).

tff(c_3216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2195,c_3213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.98  
% 5.19/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/1.98  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.19/1.98  
% 5.19/1.98  %Foreground sorts:
% 5.19/1.98  
% 5.19/1.98  
% 5.19/1.98  %Background operators:
% 5.19/1.98  
% 5.19/1.98  
% 5.19/1.98  %Foreground operators:
% 5.19/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.19/1.98  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.19/1.98  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.98  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.19/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.19/1.98  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.19/1.98  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.19/1.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.19/1.98  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.19/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.19/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.19/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.19/1.98  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.19/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.19/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/1.98  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.19/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.19/1.98  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.19/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.98  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.19/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.19/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/1.98  
% 5.52/2.01  tff(f_129, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.52/2.01  tff(f_79, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.52/2.01  tff(f_28, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.52/2.01  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.52/2.01  tff(f_150, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.52/2.01  tff(f_127, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.52/2.01  tff(f_107, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.52/2.01  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.52/2.01  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.52/2.01  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.52/2.01  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.52/2.01  tff(f_137, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.52/2.01  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.52/2.01  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.52/2.01  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.52/2.01  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.52/2.01  tff(c_42, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.52/2.01  tff(c_22, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.52/2.01  tff(c_55, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_22])).
% 5.52/2.01  tff(c_2, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.52/2.01  tff(c_2173, plain, (![A_170, B_171, C_172, D_173]: (r2_relset_1(A_170, B_171, C_172, C_172) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.52/2.01  tff(c_2187, plain, (![A_174, B_175, C_176]: (r2_relset_1(A_174, B_175, C_176, C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(resolution, [status(thm)], [c_2, c_2173])).
% 5.52/2.01  tff(c_2195, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_55, c_2187])).
% 5.52/2.01  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.52/2.01  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.52/2.01  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.52/2.01  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.52/2.01  tff(c_2217, plain, (![A_183, B_184]: (k2_funct_2(A_183, B_184)=k2_funct_1(B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_184, A_183, A_183) | ~v1_funct_2(B_184, A_183, A_183) | ~v1_funct_1(B_184))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.52/2.01  tff(c_2223, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2217])).
% 5.52/2.01  tff(c_2231, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2223])).
% 5.52/2.01  tff(c_2201, plain, (![A_181, B_182]: (v1_funct_1(k2_funct_2(A_181, B_182)) | ~m1_subset_1(B_182, k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))) | ~v3_funct_2(B_182, A_181, A_181) | ~v1_funct_2(B_182, A_181, A_181) | ~v1_funct_1(B_182))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_2207, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2201])).
% 5.52/2.01  tff(c_2215, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2207])).
% 5.52/2.01  tff(c_2233, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2231, c_2215])).
% 5.52/2.01  tff(c_70, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.52/2.01  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_70])).
% 5.52/2.01  tff(c_2107, plain, (![C_158, A_159, B_160]: (v2_funct_1(C_158) | ~v3_funct_2(C_158, A_159, B_160) | ~v1_funct_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.52/2.01  tff(c_2113, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2107])).
% 5.52/2.01  tff(c_2121, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2113])).
% 5.52/2.01  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.52/2.01  tff(c_2405, plain, (![A_201, B_202]: (m1_subset_1(k2_funct_2(A_201, B_202), k1_zfmisc_1(k2_zfmisc_1(A_201, A_201))) | ~m1_subset_1(B_202, k1_zfmisc_1(k2_zfmisc_1(A_201, A_201))) | ~v3_funct_2(B_202, A_201, A_201) | ~v1_funct_2(B_202, A_201, A_201) | ~v1_funct_1(B_202))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_2438, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2231, c_2405])).
% 5.52/2.01  tff(c_2453, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_2438])).
% 5.52/2.01  tff(c_4, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.52/2.01  tff(c_2480, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_2453, c_4])).
% 5.52/2.01  tff(c_2509, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2480])).
% 5.52/2.01  tff(c_2259, plain, (![A_195, B_196]: (v3_funct_2(k2_funct_2(A_195, B_196), A_195, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_196, A_195, A_195) | ~v1_funct_2(B_196, A_195, A_195) | ~v1_funct_1(B_196))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_2263, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2259])).
% 5.52/2.01  tff(c_2270, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2231, c_2263])).
% 5.52/2.01  tff(c_26, plain, (![C_24, A_22, B_23]: (v2_funct_1(C_24) | ~v3_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.52/2.01  tff(c_2474, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2453, c_26])).
% 5.52/2.01  tff(c_2505, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2233, c_2270, c_2474])).
% 5.52/2.01  tff(c_2244, plain, (![A_191, B_192]: (v1_funct_2(k2_funct_2(A_191, B_192), A_191, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))) | ~v3_funct_2(B_192, A_191, A_191) | ~v1_funct_2(B_192, A_191, A_191) | ~v1_funct_1(B_192))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_2248, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2244])).
% 5.52/2.01  tff(c_2255, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2231, c_2248])).
% 5.52/2.01  tff(c_44, plain, (![A_36, B_37]: (k1_relset_1(A_36, A_36, B_37)=A_36 | ~m1_subset_1(B_37, k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))) | ~v1_funct_2(B_37, A_36, A_36) | ~v1_funct_1(B_37))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.52/2.01  tff(c_2468, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2453, c_44])).
% 5.52/2.01  tff(c_2499, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2233, c_2255, c_2468])).
% 5.52/2.01  tff(c_18, plain, (![A_14, B_15, C_16]: (k1_relset_1(A_14, B_15, C_16)=k1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.52/2.01  tff(c_2506, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2453, c_18])).
% 5.52/2.01  tff(c_2590, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2499, c_2506])).
% 5.52/2.01  tff(c_14, plain, (![A_10]: (k2_funct_1(k2_funct_1(A_10))=A_10 | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.52/2.01  tff(c_10, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.52/2.01  tff(c_2083, plain, (![A_156]: (k5_relat_1(A_156, k2_funct_1(A_156))=k6_partfun1(k1_relat_1(A_156)) | ~v2_funct_1(A_156) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 5.52/2.01  tff(c_2092, plain, (![A_10]: (k6_partfun1(k1_relat_1(k2_funct_1(A_10)))=k5_relat_1(k2_funct_1(A_10), A_10) | ~v2_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2083])).
% 5.52/2.01  tff(c_2594, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2590, c_2092])).
% 5.52/2.01  tff(c_2598, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_54, c_2121, c_2509, c_2233, c_2505, c_2594])).
% 5.52/2.01  tff(c_30, plain, (![A_25, B_26]: (m1_subset_1(k2_funct_2(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~v3_funct_2(B_26, A_25, A_25) | ~v1_funct_2(B_26, A_25, A_25) | ~v1_funct_1(B_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_2531, plain, (![D_205, F_203, E_206, C_204, A_208, B_207]: (k1_partfun1(A_208, B_207, C_204, D_205, E_206, F_203)=k5_relat_1(E_206, F_203) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(C_204, D_205))) | ~v1_funct_1(F_203) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_1(E_206))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.52/2.01  tff(c_2539, plain, (![A_208, B_207, E_206]: (k1_partfun1(A_208, B_207, '#skF_2', '#skF_2', E_206, '#skF_3')=k5_relat_1(E_206, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_1(E_206))), inference(resolution, [status(thm)], [c_48, c_2531])).
% 5.52/2.01  tff(c_2564, plain, (![A_209, B_210, E_211]: (k1_partfun1(A_209, B_210, '#skF_2', '#skF_2', E_211, '#skF_3')=k5_relat_1(E_211, '#skF_3') | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_1(E_211))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2539])).
% 5.52/2.01  tff(c_3123, plain, (![A_223, B_224]: (k1_partfun1(A_223, A_223, '#skF_2', '#skF_2', k2_funct_2(A_223, B_224), '#skF_3')=k5_relat_1(k2_funct_2(A_223, B_224), '#skF_3') | ~v1_funct_1(k2_funct_2(A_223, B_224)) | ~m1_subset_1(B_224, k1_zfmisc_1(k2_zfmisc_1(A_223, A_223))) | ~v3_funct_2(B_224, A_223, A_223) | ~v1_funct_2(B_224, A_223, A_223) | ~v1_funct_1(B_224))), inference(resolution, [status(thm)], [c_30, c_2564])).
% 5.52/2.01  tff(c_3133, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_3123])).
% 5.52/2.01  tff(c_3147, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2233, c_2231, c_2598, c_2231, c_2231, c_3133])).
% 5.52/2.01  tff(c_212, plain, (![A_68, B_69, C_70, D_71]: (r2_relset_1(A_68, B_69, C_70, C_70) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.52/2.01  tff(c_222, plain, (![A_72, C_73]: (r2_relset_1(A_72, A_72, C_73, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, A_72))))), inference(resolution, [status(thm)], [c_55, c_212])).
% 5.52/2.01  tff(c_230, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_55, c_222])).
% 5.52/2.01  tff(c_178, plain, (![C_60, A_61, B_62]: (v2_funct_1(C_60) | ~v3_funct_2(C_60, A_61, B_62) | ~v1_funct_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.52/2.01  tff(c_184, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_178])).
% 5.52/2.01  tff(c_192, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_184])).
% 5.52/2.01  tff(c_303, plain, (![A_89, B_90]: (k2_funct_2(A_89, B_90)=k2_funct_1(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v3_funct_2(B_90, A_89, A_89) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.52/2.01  tff(c_309, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_303])).
% 5.52/2.01  tff(c_317, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_309])).
% 5.52/2.01  tff(c_416, plain, (![A_103, B_104]: (m1_subset_1(k2_funct_2(A_103, B_104), k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v3_funct_2(B_104, A_103, A_103) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_449, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_317, c_416])).
% 5.52/2.01  tff(c_464, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_449])).
% 5.52/2.01  tff(c_491, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_464, c_4])).
% 5.52/2.01  tff(c_520, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_491])).
% 5.52/2.01  tff(c_274, plain, (![A_81, B_82]: (v1_funct_1(k2_funct_2(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(k2_zfmisc_1(A_81, A_81))) | ~v3_funct_2(B_82, A_81, A_81) | ~v1_funct_2(B_82, A_81, A_81) | ~v1_funct_1(B_82))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_280, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_274])).
% 5.52/2.01  tff(c_288, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_280])).
% 5.52/2.01  tff(c_319, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_288])).
% 5.52/2.01  tff(c_342, plain, (![A_99, B_100]: (v3_funct_2(k2_funct_2(A_99, B_100), A_99, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_346, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_342])).
% 5.52/2.01  tff(c_353, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_317, c_346])).
% 5.52/2.01  tff(c_485, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_464, c_26])).
% 5.52/2.01  tff(c_516, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_353, c_485])).
% 5.52/2.01  tff(c_325, plain, (![A_91, B_92]: (v1_funct_2(k2_funct_2(A_91, B_92), A_91, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_329, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_325])).
% 5.52/2.01  tff(c_336, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_317, c_329])).
% 5.52/2.01  tff(c_40, plain, (![A_33, B_34]: (k2_funct_2(A_33, B_34)=k2_funct_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v3_funct_2(B_34, A_33, A_33) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.52/2.01  tff(c_471, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_464, c_40])).
% 5.52/2.01  tff(c_503, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_336, c_353, c_471])).
% 5.52/2.01  tff(c_443, plain, (![A_103, B_104]: (v1_relat_1(k2_funct_2(A_103, B_104)) | ~v1_relat_1(k2_zfmisc_1(A_103, A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v3_funct_2(B_104, A_103, A_103) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(resolution, [status(thm)], [c_416, c_4])).
% 5.52/2.01  tff(c_611, plain, (![A_114, B_115]: (v1_relat_1(k2_funct_2(A_114, B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_zfmisc_1(A_114, A_114))) | ~v3_funct_2(B_115, A_114, A_114) | ~v1_funct_2(B_115, A_114, A_114) | ~v1_funct_1(B_115))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_443])).
% 5.52/2.01  tff(c_614, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_464, c_611])).
% 5.52/2.01  tff(c_630, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_336, c_353, c_503, c_614])).
% 5.52/2.01  tff(c_36, plain, (![A_25, B_26]: (v1_funct_1(k2_funct_2(A_25, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~v3_funct_2(B_26, A_25, A_25) | ~v1_funct_2(B_26, A_25, A_25) | ~v1_funct_1(B_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_474, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_464, c_36])).
% 5.52/2.01  tff(c_506, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_336, c_353, c_474])).
% 5.52/2.01  tff(c_574, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_506])).
% 5.52/2.01  tff(c_32, plain, (![A_25, B_26]: (v3_funct_2(k2_funct_2(A_25, B_26), A_25, A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~v3_funct_2(B_26, A_25, A_25) | ~v1_funct_2(B_26, A_25, A_25) | ~v1_funct_1(B_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_466, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_464, c_32])).
% 5.52/2.01  tff(c_497, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_336, c_353, c_466])).
% 5.52/2.01  tff(c_589, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_497])).
% 5.52/2.01  tff(c_578, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_503, c_30])).
% 5.52/2.01  tff(c_582, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_336, c_353, c_464, c_578])).
% 5.52/2.01  tff(c_738, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_582, c_26])).
% 5.52/2.01  tff(c_781, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_589, c_738])).
% 5.52/2.01  tff(c_34, plain, (![A_25, B_26]: (v1_funct_2(k2_funct_2(A_25, B_26), A_25, A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~v3_funct_2(B_26, A_25, A_25) | ~v1_funct_2(B_26, A_25, A_25) | ~v1_funct_1(B_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.52/2.01  tff(c_468, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_464, c_34])).
% 5.52/2.01  tff(c_500, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_319, c_336, c_353, c_468])).
% 5.52/2.01  tff(c_595, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_500])).
% 5.52/2.01  tff(c_730, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_582, c_44])).
% 5.52/2.01  tff(c_774, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_574, c_595, c_730])).
% 5.52/2.01  tff(c_782, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_582, c_18])).
% 5.52/2.01  tff(c_1049, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_782])).
% 5.52/2.01  tff(c_724, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_582, c_40])).
% 5.52/2.01  tff(c_768, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_574, c_595, c_589, c_724])).
% 5.52/2.01  tff(c_866, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_768])).
% 5.52/2.01  tff(c_872, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_54, c_192, c_317, c_866])).
% 5.52/2.01  tff(c_8, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.52/2.01  tff(c_154, plain, (![A_58]: (k5_relat_1(k2_funct_1(A_58), A_58)=k6_partfun1(k2_relat_1(A_58)) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 5.52/2.01  tff(c_1064, plain, (![A_124]: (k6_partfun1(k2_relat_1(k2_funct_1(A_124)))=k5_relat_1(A_124, k2_funct_1(A_124)) | ~v2_funct_1(k2_funct_1(A_124)) | ~v1_funct_1(k2_funct_1(A_124)) | ~v1_relat_1(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_14, c_154])).
% 5.52/2.01  tff(c_1126, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_872, c_1064])).
% 5.52/2.01  tff(c_1142, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_574, c_781, c_520, c_872, c_319, c_872, c_516, c_872, c_872, c_1126])).
% 5.52/2.01  tff(c_166, plain, (![A_59]: (k5_relat_1(A_59, k2_funct_1(A_59))=k6_partfun1(k1_relat_1(A_59)) | ~v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_10])).
% 5.52/2.01  tff(c_175, plain, (![A_10]: (k6_partfun1(k1_relat_1(k2_funct_1(A_10)))=k5_relat_1(k2_funct_1(A_10), A_10) | ~v2_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_166])).
% 5.52/2.01  tff(c_1207, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1142, c_175])).
% 5.52/2.01  tff(c_1223, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_319, c_516, c_630, c_574, c_781, c_1049, c_1207])).
% 5.52/2.01  tff(c_163, plain, (![A_10]: (k6_partfun1(k2_relat_1(k2_funct_1(A_10)))=k5_relat_1(A_10, k2_funct_1(A_10)) | ~v2_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_154])).
% 5.52/2.01  tff(c_1268, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1223, c_163])).
% 5.52/2.01  tff(c_1313, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_54, c_192, c_520, c_319, c_516, c_1268])).
% 5.52/2.01  tff(c_523, plain, (![E_108, A_110, F_105, D_107, B_109, C_106]: (k1_partfun1(A_110, B_109, C_106, D_107, E_108, F_105)=k5_relat_1(E_108, F_105) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_106, D_107))) | ~v1_funct_1(F_105) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_1(E_108))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.52/2.01  tff(c_525, plain, (![A_110, B_109, E_108]: (k1_partfun1(A_110, B_109, '#skF_2', '#skF_2', E_108, k2_funct_1('#skF_3'))=k5_relat_1(E_108, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))) | ~v1_funct_1(E_108))), inference(resolution, [status(thm)], [c_464, c_523])).
% 5.52/2.01  tff(c_1956, plain, (![A_141, B_142, E_143]: (k1_partfun1(A_141, B_142, '#skF_2', '#skF_2', E_143, k2_funct_1('#skF_3'))=k5_relat_1(E_143, k2_funct_1('#skF_3')) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_525])).
% 5.52/2.01  tff(c_1986, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1956])).
% 5.52/2.01  tff(c_2006, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1313, c_1986])).
% 5.52/2.01  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.52/2.01  tff(c_84, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.52/2.01  tff(c_320, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_84])).
% 5.52/2.01  tff(c_2008, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2006, c_320])).
% 5.52/2.01  tff(c_2011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_2008])).
% 5.52/2.01  tff(c_2012, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 5.52/2.01  tff(c_2235, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2231, c_2012])).
% 5.52/2.01  tff(c_3213, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_2235])).
% 5.52/2.01  tff(c_3216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2195, c_3213])).
% 5.52/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.52/2.01  
% 5.52/2.01  Inference rules
% 5.52/2.01  ----------------------
% 5.52/2.01  #Ref     : 0
% 5.52/2.01  #Sup     : 755
% 5.52/2.01  #Fact    : 0
% 5.52/2.01  #Define  : 0
% 5.52/2.01  #Split   : 2
% 5.52/2.01  #Chain   : 0
% 5.52/2.01  #Close   : 0
% 5.52/2.01  
% 5.52/2.01  Ordering : KBO
% 5.52/2.01  
% 5.52/2.01  Simplification rules
% 5.52/2.01  ----------------------
% 5.52/2.01  #Subsume      : 93
% 5.52/2.01  #Demod        : 1370
% 5.52/2.01  #Tautology    : 316
% 5.52/2.01  #SimpNegUnit  : 0
% 5.52/2.01  #BackRed      : 27
% 5.52/2.01  
% 5.52/2.01  #Partial instantiations: 0
% 5.52/2.01  #Strategies tried      : 1
% 5.52/2.01  
% 5.52/2.01  Timing (in seconds)
% 5.52/2.01  ----------------------
% 5.52/2.01  Preprocessing        : 0.34
% 5.52/2.01  Parsing              : 0.18
% 5.52/2.01  CNF conversion       : 0.02
% 5.52/2.01  Main loop            : 0.86
% 5.52/2.01  Inferencing          : 0.28
% 5.52/2.01  Reduction            : 0.34
% 5.52/2.01  Demodulation         : 0.26
% 5.52/2.01  BG Simplification    : 0.04
% 5.52/2.01  Subsumption          : 0.14
% 5.52/2.01  Abstraction          : 0.04
% 5.52/2.01  MUC search           : 0.00
% 5.52/2.01  Cooper               : 0.00
% 5.52/2.01  Total                : 1.26
% 5.52/2.01  Index Insertion      : 0.00
% 5.52/2.01  Index Deletion       : 0.00
% 5.52/2.01  Index Matching       : 0.00
% 5.52/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
