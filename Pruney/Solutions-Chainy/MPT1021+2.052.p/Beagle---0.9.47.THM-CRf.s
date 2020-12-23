%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:07 EST 2020

% Result     : Theorem 5.71s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :  193 (6961 expanded)
%              Number of leaves         :   40 (2815 expanded)
%              Depth                    :   23
%              Number of atoms          :  436 (25427 expanded)
%              Number of equality atoms :   67 (1300 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_103,axiom,(
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

tff(f_144,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_50,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_2311,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( r2_relset_1(A_204,B_205,C_206,C_206)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2362,plain,(
    ! [A_212,C_213] :
      ( r2_relset_1(A_212,A_212,C_213,C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_212,A_212))) ) ),
    inference(resolution,[status(thm)],[c_63,c_2311])).

tff(c_2371,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_63,c_2362])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2171,plain,(
    ! [C_176,A_177,B_178] :
      ( v1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2179,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2171])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2273,plain,(
    ! [C_192,A_193,B_194] :
      ( v2_funct_1(C_192)
      | ~ v3_funct_2(C_192,A_193,B_194)
      | ~ v1_funct_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2282,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2273])).

tff(c_2289,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2282])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2408,plain,(
    ! [A_221,B_222] :
      ( k2_funct_2(A_221,B_222) = k2_funct_1(B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ v3_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2418,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2408])).

tff(c_2425,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2418])).

tff(c_2471,plain,(
    ! [A_235,B_236] :
      ( m1_subset_1(k2_funct_2(A_235,B_236),k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ v3_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2501,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2425,c_2471])).

tff(c_2513,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_2501])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2564,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_14])).

tff(c_2376,plain,(
    ! [A_215,B_216] :
      ( v1_funct_1(k2_funct_2(A_215,B_216))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215)))
      | ~ v3_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2386,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2376])).

tff(c_2393,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2386])).

tff(c_2426,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_2393])).

tff(c_2436,plain,(
    ! [A_226,B_227] :
      ( v3_funct_2(k2_funct_2(A_226,B_227),A_226,A_226)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ v3_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_1(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2443,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2436])).

tff(c_2450,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2425,c_2443])).

tff(c_24,plain,(
    ! [C_18,A_16,B_17] :
      ( v2_funct_1(C_18)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2534,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_24])).

tff(c_2562,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2450,c_2534])).

tff(c_2452,plain,(
    ! [A_229,B_230] :
      ( v1_funct_2(k2_funct_2(A_229,B_230),A_229,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(k2_zfmisc_1(A_229,A_229)))
      | ~ v3_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_2(B_230,A_229,A_229)
      | ~ v1_funct_1(B_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2459,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2452])).

tff(c_2466,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2425,c_2459])).

tff(c_52,plain,(
    ! [A_33,B_34] :
      ( k1_relset_1(A_33,A_33,B_34) = A_33
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2528,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_52])).

tff(c_2556,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2466,c_2528])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2563,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_16])).

tff(c_2618,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2556,c_2563])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( k2_funct_2(A_30,B_31) = k2_funct_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2520,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_48])).

tff(c_2549,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2466,c_2450,c_2520])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_funct_2(A_19,B_20),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2573,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2549,c_28])).

tff(c_2577,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2466,c_2450,c_2513,c_2573])).

tff(c_2714,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2577,c_14])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k2_funct_2(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2525,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_34])).

tff(c_2553,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2466,c_2450,c_2525])).

tff(c_2569,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2553])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v3_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2517,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_30])).

tff(c_2546,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2466,c_2450,c_2517])).

tff(c_2606,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2546])).

tff(c_2675,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2577,c_24])).

tff(c_2712,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_2606,c_2675])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( v1_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2515,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2513,c_32])).

tff(c_2543,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2466,c_2450,c_2515])).

tff(c_2612,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2543])).

tff(c_2661,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2577,c_48])).

tff(c_2699,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_2612,c_2606,c_2661])).

tff(c_2791,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2699])).

tff(c_2797,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2179,c_62,c_2289,c_2425,c_2791])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_2863,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2797,c_65])).

tff(c_2890,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2714,c_2569,c_2712,c_2863])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_3057,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2890,c_64])).

tff(c_3067,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_2426,c_2562,c_2618,c_3057])).

tff(c_3073,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3067,c_2890])).

tff(c_3194,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3073])).

tff(c_3202,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2179,c_62,c_2289,c_3194])).

tff(c_2584,plain,(
    ! [D_242,A_241,E_239,B_238,C_237,F_240] :
      ( k1_partfun1(A_241,B_238,C_237,D_242,E_239,F_240) = k5_relat_1(E_239,F_240)
      | ~ m1_subset_1(F_240,k1_zfmisc_1(k2_zfmisc_1(C_237,D_242)))
      | ~ v1_funct_1(F_240)
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(A_241,B_238)))
      | ~ v1_funct_1(E_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2594,plain,(
    ! [A_241,B_238,E_239] :
      ( k1_partfun1(A_241,B_238,'#skF_2','#skF_2',E_239,'#skF_3') = k5_relat_1(E_239,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(A_241,B_238)))
      | ~ v1_funct_1(E_239) ) ),
    inference(resolution,[status(thm)],[c_56,c_2584])).

tff(c_2623,plain,(
    ! [A_243,B_244,E_245] :
      ( k1_partfun1(A_243,B_244,'#skF_2','#skF_2',E_245,'#skF_3') = k5_relat_1(E_245,'#skF_3')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(E_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2594])).

tff(c_3026,plain,(
    ! [A_251,B_252] :
      ( k1_partfun1(A_251,A_251,'#skF_2','#skF_2',k2_funct_2(A_251,B_252),'#skF_3') = k5_relat_1(k2_funct_2(A_251,B_252),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_251,B_252))
      | ~ m1_subset_1(B_252,k1_zfmisc_1(k2_zfmisc_1(A_251,A_251)))
      | ~ v3_funct_2(B_252,A_251,A_251)
      | ~ v1_funct_2(B_252,A_251,A_251)
      | ~ v1_funct_1(B_252) ) ),
    inference(resolution,[status(thm)],[c_28,c_2623])).

tff(c_3039,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3026])).

tff(c_3053,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2426,c_2425,c_2425,c_2425,c_3039])).

tff(c_3271,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3202,c_3053])).

tff(c_223,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( r2_relset_1(A_75,B_76,C_77,C_77)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_274,plain,(
    ! [A_83,C_84] :
      ( r2_relset_1(A_83,A_83,C_84,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83))) ) ),
    inference(resolution,[status(thm)],[c_63,c_223])).

tff(c_283,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_63,c_274])).

tff(c_83,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_185,plain,(
    ! [C_63,A_64,B_65] :
      ( v2_funct_1(C_63)
      | ~ v3_funct_2(C_63,A_64,B_65)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_194,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_185])).

tff(c_201,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_194])).

tff(c_320,plain,(
    ! [A_92,B_93] :
      ( k2_funct_2(A_92,B_93) = k2_funct_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_330,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_320])).

tff(c_337,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_330])).

tff(c_288,plain,(
    ! [A_86,B_87] :
      ( v1_funct_1(k2_funct_2(A_86,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k2_zfmisc_1(A_86,A_86)))
      | ~ v3_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_2(B_87,A_86,A_86)
      | ~ v1_funct_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_298,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_288])).

tff(c_305,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_298])).

tff(c_338,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_305])).

tff(c_347,plain,(
    ! [A_97,B_98] :
      ( v1_funct_2(k2_funct_2(A_97,B_98),A_97,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v3_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_354,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_347])).

tff(c_361,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_337,c_354])).

tff(c_364,plain,(
    ! [A_101,B_102] :
      ( v3_funct_2(k2_funct_2(A_101,B_102),A_101,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k2_zfmisc_1(A_101,A_101)))
      | ~ v3_funct_2(B_102,A_101,A_101)
      | ~ v1_funct_2(B_102,A_101,A_101)
      | ~ v1_funct_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_371,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_364])).

tff(c_378,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_337,c_371])).

tff(c_383,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k2_funct_2(A_107,B_108),k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ v3_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_2(B_108,A_107,A_107)
      | ~ v1_funct_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_413,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_383])).

tff(c_425,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_413])).

tff(c_432,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_48])).

tff(c_461,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_361,c_378,c_432])).

tff(c_437,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_34])).

tff(c_465,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_361,c_378,c_437])).

tff(c_482,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_465])).

tff(c_429,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_32])).

tff(c_458,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_361,c_378,c_429])).

tff(c_481,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_458])).

tff(c_486,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_28])).

tff(c_490,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_361,c_378,c_425,c_486])).

tff(c_581,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_490,c_52])).

tff(c_618,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_481,c_581])).

tff(c_625,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_490,c_16])).

tff(c_847,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_625])).

tff(c_626,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_490,c_14])).

tff(c_427,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_30])).

tff(c_455,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_361,c_378,c_427])).

tff(c_524,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_455])).

tff(c_587,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_490,c_24])).

tff(c_624,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_524,c_587])).

tff(c_573,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_490,c_48])).

tff(c_611,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_481,c_524,c_573])).

tff(c_743,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_611])).

tff(c_749,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_62,c_201,c_337,c_743])).

tff(c_779,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_64])).

tff(c_807,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_482,c_624,c_779])).

tff(c_857,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_807])).

tff(c_868,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_857])).

tff(c_876,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_62,c_201,c_868])).

tff(c_492,plain,(
    ! [A_113,E_111,F_112,B_110,C_109,D_114] :
      ( k1_partfun1(A_113,B_110,C_109,D_114,E_111,F_112) = k5_relat_1(E_111,F_112)
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_109,D_114)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_494,plain,(
    ! [A_113,B_110,E_111] :
      ( k1_partfun1(A_113,B_110,'#skF_2','#skF_2',E_111,k2_funct_1('#skF_3')) = k5_relat_1(E_111,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(resolution,[status(thm)],[c_425,c_492])).

tff(c_2109,plain,(
    ! [A_170,B_171,E_172] :
      ( k1_partfun1(A_170,B_171,'#skF_2','#skF_2',E_172,k2_funct_1('#skF_3')) = k5_relat_1(E_172,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_1(E_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_494])).

tff(c_2142,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2109])).

tff(c_2161,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_876,c_2142])).

tff(c_54,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_339,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_79])).

tff(c_2162,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2161,c_339])).

tff(c_2165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_2162])).

tff(c_2166,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2428,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_2166])).

tff(c_3272,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_2428])).

tff(c_3275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_3272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.71/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.12  
% 5.80/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.12  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.80/2.12  
% 5.80/2.12  %Foreground sorts:
% 5.80/2.12  
% 5.80/2.12  
% 5.80/2.12  %Background operators:
% 5.80/2.12  
% 5.80/2.12  
% 5.80/2.12  %Foreground operators:
% 5.80/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.12  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.80/2.12  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.80/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.12  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.80/2.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.80/2.12  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.80/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.80/2.12  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.80/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.80/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.12  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.80/2.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.80/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.80/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.12  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.80/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.80/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.80/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.80/2.12  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.80/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.80/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.80/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.12  
% 5.94/2.15  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.94/2.15  tff(f_75, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.94/2.15  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.94/2.15  tff(f_157, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.94/2.15  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.94/2.15  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.94/2.15  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.94/2.15  tff(f_134, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.94/2.15  tff(f_103, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.94/2.15  tff(f_144, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.94/2.15  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.94/2.15  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.94/2.15  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.94/2.15  tff(c_50, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.94/2.15  tff(c_20, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.94/2.15  tff(c_63, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 5.94/2.15  tff(c_2311, plain, (![A_204, B_205, C_206, D_207]: (r2_relset_1(A_204, B_205, C_206, C_206) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.94/2.15  tff(c_2362, plain, (![A_212, C_213]: (r2_relset_1(A_212, A_212, C_213, C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_212, A_212))))), inference(resolution, [status(thm)], [c_63, c_2311])).
% 5.94/2.15  tff(c_2371, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_63, c_2362])).
% 5.94/2.15  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.94/2.15  tff(c_2171, plain, (![C_176, A_177, B_178]: (v1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.94/2.15  tff(c_2179, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2171])).
% 5.94/2.15  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.94/2.15  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.94/2.15  tff(c_2273, plain, (![C_192, A_193, B_194]: (v2_funct_1(C_192) | ~v3_funct_2(C_192, A_193, B_194) | ~v1_funct_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.94/2.15  tff(c_2282, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2273])).
% 5.94/2.15  tff(c_2289, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2282])).
% 5.94/2.15  tff(c_12, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.15  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.94/2.15  tff(c_2408, plain, (![A_221, B_222]: (k2_funct_2(A_221, B_222)=k2_funct_1(B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~v3_funct_2(B_222, A_221, A_221) | ~v1_funct_2(B_222, A_221, A_221) | ~v1_funct_1(B_222))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.94/2.15  tff(c_2418, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2408])).
% 5.94/2.15  tff(c_2425, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2418])).
% 5.94/2.15  tff(c_2471, plain, (![A_235, B_236]: (m1_subset_1(k2_funct_2(A_235, B_236), k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~v3_funct_2(B_236, A_235, A_235) | ~v1_funct_2(B_236, A_235, A_235) | ~v1_funct_1(B_236))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2501, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2425, c_2471])).
% 5.94/2.15  tff(c_2513, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_2501])).
% 5.94/2.15  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.94/2.15  tff(c_2564, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_14])).
% 5.94/2.15  tff(c_2376, plain, (![A_215, B_216]: (v1_funct_1(k2_funct_2(A_215, B_216)) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))) | ~v3_funct_2(B_216, A_215, A_215) | ~v1_funct_2(B_216, A_215, A_215) | ~v1_funct_1(B_216))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2386, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2376])).
% 5.94/2.15  tff(c_2393, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2386])).
% 5.94/2.15  tff(c_2426, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_2393])).
% 5.94/2.15  tff(c_2436, plain, (![A_226, B_227]: (v3_funct_2(k2_funct_2(A_226, B_227), A_226, A_226) | ~m1_subset_1(B_227, k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~v3_funct_2(B_227, A_226, A_226) | ~v1_funct_2(B_227, A_226, A_226) | ~v1_funct_1(B_227))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2443, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2436])).
% 5.94/2.15  tff(c_2450, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2425, c_2443])).
% 5.94/2.15  tff(c_24, plain, (![C_18, A_16, B_17]: (v2_funct_1(C_18) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.94/2.15  tff(c_2534, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_24])).
% 5.94/2.15  tff(c_2562, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2450, c_2534])).
% 5.94/2.15  tff(c_2452, plain, (![A_229, B_230]: (v1_funct_2(k2_funct_2(A_229, B_230), A_229, A_229) | ~m1_subset_1(B_230, k1_zfmisc_1(k2_zfmisc_1(A_229, A_229))) | ~v3_funct_2(B_230, A_229, A_229) | ~v1_funct_2(B_230, A_229, A_229) | ~v1_funct_1(B_230))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2459, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2452])).
% 5.94/2.15  tff(c_2466, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2425, c_2459])).
% 5.94/2.15  tff(c_52, plain, (![A_33, B_34]: (k1_relset_1(A_33, A_33, B_34)=A_33 | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.94/2.15  tff(c_2528, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_52])).
% 5.94/2.15  tff(c_2556, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2466, c_2528])).
% 5.94/2.15  tff(c_16, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.94/2.15  tff(c_2563, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_16])).
% 5.94/2.15  tff(c_2618, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2556, c_2563])).
% 5.94/2.15  tff(c_48, plain, (![A_30, B_31]: (k2_funct_2(A_30, B_31)=k2_funct_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.94/2.15  tff(c_2520, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_48])).
% 5.94/2.15  tff(c_2549, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2466, c_2450, c_2520])).
% 5.94/2.15  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k2_funct_2(A_19, B_20), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2573, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2549, c_28])).
% 5.94/2.15  tff(c_2577, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2466, c_2450, c_2513, c_2573])).
% 5.94/2.15  tff(c_2714, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2577, c_14])).
% 5.94/2.15  tff(c_34, plain, (![A_19, B_20]: (v1_funct_1(k2_funct_2(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2525, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_34])).
% 5.94/2.15  tff(c_2553, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2466, c_2450, c_2525])).
% 5.94/2.15  tff(c_2569, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2553])).
% 5.94/2.15  tff(c_30, plain, (![A_19, B_20]: (v3_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2517, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_30])).
% 5.94/2.15  tff(c_2546, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2466, c_2450, c_2517])).
% 5.94/2.15  tff(c_2606, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2546])).
% 5.94/2.15  tff(c_2675, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2577, c_24])).
% 5.94/2.15  tff(c_2712, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2569, c_2606, c_2675])).
% 5.94/2.15  tff(c_32, plain, (![A_19, B_20]: (v1_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_2515, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2513, c_32])).
% 5.94/2.15  tff(c_2543, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2466, c_2450, c_2515])).
% 5.94/2.15  tff(c_2612, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2543])).
% 5.94/2.15  tff(c_2661, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2577, c_48])).
% 5.94/2.15  tff(c_2699, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2569, c_2612, c_2606, c_2661])).
% 5.94/2.15  tff(c_2791, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2699])).
% 5.94/2.15  tff(c_2797, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2179, c_62, c_2289, c_2425, c_2791])).
% 5.94/2.15  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.94/2.15  tff(c_65, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 5.94/2.15  tff(c_2863, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2797, c_65])).
% 5.94/2.15  tff(c_2890, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2714, c_2569, c_2712, c_2863])).
% 5.94/2.15  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.94/2.15  tff(c_64, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8])).
% 5.94/2.15  tff(c_3057, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2890, c_64])).
% 5.94/2.15  tff(c_3067, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2564, c_2426, c_2562, c_2618, c_3057])).
% 5.94/2.15  tff(c_3073, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3067, c_2890])).
% 5.94/2.15  tff(c_3194, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_3073])).
% 5.94/2.15  tff(c_3202, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2179, c_62, c_2289, c_3194])).
% 5.94/2.15  tff(c_2584, plain, (![D_242, A_241, E_239, B_238, C_237, F_240]: (k1_partfun1(A_241, B_238, C_237, D_242, E_239, F_240)=k5_relat_1(E_239, F_240) | ~m1_subset_1(F_240, k1_zfmisc_1(k2_zfmisc_1(C_237, D_242))) | ~v1_funct_1(F_240) | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(A_241, B_238))) | ~v1_funct_1(E_239))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.94/2.15  tff(c_2594, plain, (![A_241, B_238, E_239]: (k1_partfun1(A_241, B_238, '#skF_2', '#skF_2', E_239, '#skF_3')=k5_relat_1(E_239, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(A_241, B_238))) | ~v1_funct_1(E_239))), inference(resolution, [status(thm)], [c_56, c_2584])).
% 5.94/2.15  tff(c_2623, plain, (![A_243, B_244, E_245]: (k1_partfun1(A_243, B_244, '#skF_2', '#skF_2', E_245, '#skF_3')=k5_relat_1(E_245, '#skF_3') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(E_245))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2594])).
% 5.94/2.15  tff(c_3026, plain, (![A_251, B_252]: (k1_partfun1(A_251, A_251, '#skF_2', '#skF_2', k2_funct_2(A_251, B_252), '#skF_3')=k5_relat_1(k2_funct_2(A_251, B_252), '#skF_3') | ~v1_funct_1(k2_funct_2(A_251, B_252)) | ~m1_subset_1(B_252, k1_zfmisc_1(k2_zfmisc_1(A_251, A_251))) | ~v3_funct_2(B_252, A_251, A_251) | ~v1_funct_2(B_252, A_251, A_251) | ~v1_funct_1(B_252))), inference(resolution, [status(thm)], [c_28, c_2623])).
% 5.94/2.15  tff(c_3039, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_3026])).
% 5.94/2.15  tff(c_3053, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2426, c_2425, c_2425, c_2425, c_3039])).
% 5.94/2.15  tff(c_3271, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3202, c_3053])).
% 5.94/2.15  tff(c_223, plain, (![A_75, B_76, C_77, D_78]: (r2_relset_1(A_75, B_76, C_77, C_77) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.94/2.15  tff(c_274, plain, (![A_83, C_84]: (r2_relset_1(A_83, A_83, C_84, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))))), inference(resolution, [status(thm)], [c_63, c_223])).
% 5.94/2.15  tff(c_283, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_63, c_274])).
% 5.94/2.15  tff(c_83, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.94/2.15  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_83])).
% 5.94/2.15  tff(c_185, plain, (![C_63, A_64, B_65]: (v2_funct_1(C_63) | ~v3_funct_2(C_63, A_64, B_65) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.94/2.15  tff(c_194, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_185])).
% 5.94/2.15  tff(c_201, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_194])).
% 5.94/2.15  tff(c_320, plain, (![A_92, B_93]: (k2_funct_2(A_92, B_93)=k2_funct_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.94/2.15  tff(c_330, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_320])).
% 5.94/2.15  tff(c_337, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_330])).
% 5.94/2.15  tff(c_288, plain, (![A_86, B_87]: (v1_funct_1(k2_funct_2(A_86, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(k2_zfmisc_1(A_86, A_86))) | ~v3_funct_2(B_87, A_86, A_86) | ~v1_funct_2(B_87, A_86, A_86) | ~v1_funct_1(B_87))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_298, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_288])).
% 5.94/2.15  tff(c_305, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_298])).
% 5.94/2.15  tff(c_338, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_305])).
% 5.94/2.15  tff(c_347, plain, (![A_97, B_98]: (v1_funct_2(k2_funct_2(A_97, B_98), A_97, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v3_funct_2(B_98, A_97, A_97) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_354, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_347])).
% 5.94/2.15  tff(c_361, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_337, c_354])).
% 5.94/2.15  tff(c_364, plain, (![A_101, B_102]: (v3_funct_2(k2_funct_2(A_101, B_102), A_101, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(k2_zfmisc_1(A_101, A_101))) | ~v3_funct_2(B_102, A_101, A_101) | ~v1_funct_2(B_102, A_101, A_101) | ~v1_funct_1(B_102))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_371, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_364])).
% 5.94/2.15  tff(c_378, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_337, c_371])).
% 5.94/2.15  tff(c_383, plain, (![A_107, B_108]: (m1_subset_1(k2_funct_2(A_107, B_108), k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~v3_funct_2(B_108, A_107, A_107) | ~v1_funct_2(B_108, A_107, A_107) | ~v1_funct_1(B_108))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.15  tff(c_413, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_337, c_383])).
% 5.94/2.15  tff(c_425, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_413])).
% 5.94/2.15  tff(c_432, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_48])).
% 5.94/2.15  tff(c_461, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_361, c_378, c_432])).
% 5.94/2.15  tff(c_437, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_34])).
% 5.94/2.15  tff(c_465, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_361, c_378, c_437])).
% 5.94/2.15  tff(c_482, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_465])).
% 5.94/2.15  tff(c_429, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_32])).
% 5.94/2.15  tff(c_458, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_361, c_378, c_429])).
% 5.94/2.15  tff(c_481, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_458])).
% 5.94/2.15  tff(c_486, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_461, c_28])).
% 5.94/2.15  tff(c_490, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_361, c_378, c_425, c_486])).
% 5.94/2.15  tff(c_581, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_490, c_52])).
% 5.94/2.15  tff(c_618, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_481, c_581])).
% 5.94/2.15  tff(c_625, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_490, c_16])).
% 5.94/2.15  tff(c_847, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_618, c_625])).
% 5.94/2.15  tff(c_626, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_490, c_14])).
% 5.94/2.15  tff(c_427, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_30])).
% 5.94/2.15  tff(c_455, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_361, c_378, c_427])).
% 5.94/2.15  tff(c_524, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_455])).
% 5.94/2.15  tff(c_587, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_490, c_24])).
% 5.94/2.15  tff(c_624, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_524, c_587])).
% 5.94/2.15  tff(c_573, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_490, c_48])).
% 5.94/2.15  tff(c_611, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_481, c_524, c_573])).
% 5.94/2.15  tff(c_743, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_611])).
% 5.94/2.15  tff(c_749, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_62, c_201, c_337, c_743])).
% 5.94/2.15  tff(c_779, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_749, c_64])).
% 5.94/2.15  tff(c_807, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_626, c_482, c_624, c_779])).
% 5.94/2.15  tff(c_857, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_807])).
% 5.94/2.15  tff(c_868, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_857])).
% 5.94/2.15  tff(c_876, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_62, c_201, c_868])).
% 5.94/2.15  tff(c_492, plain, (![A_113, E_111, F_112, B_110, C_109, D_114]: (k1_partfun1(A_113, B_110, C_109, D_114, E_111, F_112)=k5_relat_1(E_111, F_112) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_109, D_114))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_110))) | ~v1_funct_1(E_111))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.94/2.15  tff(c_494, plain, (![A_113, B_110, E_111]: (k1_partfun1(A_113, B_110, '#skF_2', '#skF_2', E_111, k2_funct_1('#skF_3'))=k5_relat_1(E_111, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_110))) | ~v1_funct_1(E_111))), inference(resolution, [status(thm)], [c_425, c_492])).
% 5.94/2.15  tff(c_2109, plain, (![A_170, B_171, E_172]: (k1_partfun1(A_170, B_171, '#skF_2', '#skF_2', E_172, k2_funct_1('#skF_3'))=k5_relat_1(E_172, k2_funct_1('#skF_3')) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_1(E_172))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_494])).
% 5.94/2.15  tff(c_2142, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2109])).
% 5.94/2.15  tff(c_2161, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_876, c_2142])).
% 5.94/2.15  tff(c_54, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.94/2.15  tff(c_79, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.94/2.15  tff(c_339, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_79])).
% 5.94/2.15  tff(c_2162, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2161, c_339])).
% 5.94/2.15  tff(c_2165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_2162])).
% 5.94/2.15  tff(c_2166, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 5.94/2.15  tff(c_2428, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_2166])).
% 5.94/2.15  tff(c_3272, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_2428])).
% 5.94/2.15  tff(c_3275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2371, c_3272])).
% 5.94/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.15  
% 5.94/2.15  Inference rules
% 5.94/2.15  ----------------------
% 5.94/2.15  #Ref     : 0
% 5.94/2.15  #Sup     : 758
% 5.94/2.15  #Fact    : 0
% 5.94/2.15  #Define  : 0
% 5.94/2.15  #Split   : 2
% 5.94/2.15  #Chain   : 0
% 5.94/2.15  #Close   : 0
% 5.94/2.15  
% 5.94/2.15  Ordering : KBO
% 5.94/2.15  
% 5.94/2.15  Simplification rules
% 5.94/2.15  ----------------------
% 5.94/2.15  #Subsume      : 75
% 5.94/2.15  #Demod        : 1380
% 5.94/2.15  #Tautology    : 333
% 5.94/2.15  #SimpNegUnit  : 0
% 5.94/2.15  #BackRed      : 29
% 5.94/2.15  
% 5.94/2.15  #Partial instantiations: 0
% 5.94/2.16  #Strategies tried      : 1
% 5.94/2.16  
% 5.94/2.16  Timing (in seconds)
% 5.94/2.16  ----------------------
% 5.94/2.16  Preprocessing        : 0.33
% 5.94/2.16  Parsing              : 0.18
% 5.94/2.16  CNF conversion       : 0.02
% 5.94/2.16  Main loop            : 0.98
% 5.94/2.16  Inferencing          : 0.32
% 5.94/2.16  Reduction            : 0.40
% 5.94/2.16  Demodulation         : 0.31
% 5.94/2.16  BG Simplification    : 0.04
% 5.94/2.16  Subsumption          : 0.15
% 5.94/2.16  Abstraction          : 0.04
% 5.94/2.16  MUC search           : 0.00
% 5.94/2.16  Cooper               : 0.00
% 5.94/2.16  Total                : 1.39
% 5.94/2.16  Index Insertion      : 0.00
% 5.94/2.16  Index Deletion       : 0.00
% 5.94/2.16  Index Matching       : 0.00
% 5.94/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
