%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 6.26s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 347 expanded)
%              Number of leaves         :   43 ( 151 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 (1059 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2200,plain,(
    ! [C_192,A_193,B_194] :
      ( v1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2212,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2200])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2427,plain,(
    ! [C_242,A_243,B_244] :
      ( v2_funct_1(C_242)
      | ~ v3_funct_2(C_242,A_243,B_244)
      | ~ v1_funct_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2433,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2427])).

tff(c_2441,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2433])).

tff(c_40,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2489,plain,(
    ! [A_253,B_254,C_255,D_256] :
      ( r2_relset_1(A_253,B_254,C_255,C_255)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254)))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2499,plain,(
    ! [A_257,C_258] :
      ( r2_relset_1(A_257,A_257,C_258,C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_257,A_257))) ) ),
    inference(resolution,[status(thm)],[c_40,c_2489])).

tff(c_2507,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_40,c_2499])).

tff(c_2232,plain,(
    ! [C_204,B_205,A_206] :
      ( v5_relat_1(C_204,B_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2244,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2232])).

tff(c_2249,plain,(
    ! [B_211,A_212] :
      ( k2_relat_1(B_211) = A_212
      | ~ v2_funct_2(B_211,A_212)
      | ~ v5_relat_1(B_211,A_212)
      | ~ v1_relat_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2258,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2244,c_2249])).

tff(c_2267,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2212,c_2258])).

tff(c_2268,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2267])).

tff(c_2342,plain,(
    ! [C_228,B_229,A_230] :
      ( v2_funct_2(C_228,B_229)
      | ~ v3_funct_2(C_228,A_230,B_229)
      | ~ v1_funct_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_230,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2348,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2342])).

tff(c_2356,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2348])).

tff(c_2358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2268,c_2356])).

tff(c_2359,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2267])).

tff(c_46,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2545,plain,(
    ! [A_271,B_272] :
      ( k2_funct_2(A_271,B_272) = k2_funct_1(B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_zfmisc_1(A_271,A_271)))
      | ~ v3_funct_2(B_272,A_271,A_271)
      | ~ v1_funct_2(B_272,A_271,A_271)
      | ~ v1_funct_1(B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2551,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2545])).

tff(c_2559,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2551])).

tff(c_2510,plain,(
    ! [A_259,B_260] :
      ( v1_funct_1(k2_funct_2(A_259,B_260))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2516,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2510])).

tff(c_2524,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2516])).

tff(c_2561,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2524])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_funct_2(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v3_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2715,plain,(
    ! [B_289,D_285,E_290,A_286,F_288,C_287] :
      ( k1_partfun1(A_286,B_289,C_287,D_285,E_290,F_288) = k5_relat_1(E_290,F_288)
      | ~ m1_subset_1(F_288,k1_zfmisc_1(k2_zfmisc_1(C_287,D_285)))
      | ~ v1_funct_1(F_288)
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(A_286,B_289)))
      | ~ v1_funct_1(E_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2723,plain,(
    ! [A_286,B_289,E_290] :
      ( k1_partfun1(A_286,B_289,'#skF_2','#skF_2',E_290,'#skF_3') = k5_relat_1(E_290,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(A_286,B_289)))
      | ~ v1_funct_1(E_290) ) ),
    inference(resolution,[status(thm)],[c_52,c_2715])).

tff(c_2740,plain,(
    ! [A_291,B_292,E_293] :
      ( k1_partfun1(A_291,B_292,'#skF_2','#skF_2',E_293,'#skF_3') = k5_relat_1(E_293,'#skF_3')
      | ~ m1_subset_1(E_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_1(E_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2723])).

tff(c_3105,plain,(
    ! [A_307,B_308] :
      ( k1_partfun1(A_307,A_307,'#skF_2','#skF_2',k2_funct_2(A_307,B_308),'#skF_3') = k5_relat_1(k2_funct_2(A_307,B_308),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_307,B_308))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(k2_zfmisc_1(A_307,A_307)))
      | ~ v3_funct_2(B_308,A_307,A_307)
      | ~ v1_funct_2(B_308,A_307,A_307)
      | ~ v1_funct_1(B_308) ) ),
    inference(resolution,[status(thm)],[c_30,c_2740])).

tff(c_3117,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3105])).

tff(c_3134,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2561,c_2559,c_2559,c_2559,c_3117])).

tff(c_75,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_284,plain,(
    ! [C_88,A_89,B_90] :
      ( v2_funct_1(C_88)
      | ~ v3_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_290,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_284])).

tff(c_298,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_290])).

tff(c_318,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( r2_relset_1(A_96,B_97,C_98,C_98)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_328,plain,(
    ! [A_100,C_101] :
      ( r2_relset_1(A_100,A_100,C_101,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100))) ) ),
    inference(resolution,[status(thm)],[c_40,c_318])).

tff(c_336,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_40,c_328])).

tff(c_143,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_155,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_143])).

tff(c_339,plain,(
    ! [A_102,B_103] :
      ( k1_relset_1(A_102,A_102,B_103) = A_102
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_345,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_339])).

tff(c_354,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_155,c_345])).

tff(c_8,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_402,plain,(
    ! [A_117,B_118] :
      ( k2_funct_2(A_117,B_118) = k2_funct_1(B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_408,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_402])).

tff(c_416,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_408])).

tff(c_384,plain,(
    ! [A_112,B_113] :
      ( v1_funct_1(k2_funct_2(A_112,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_zfmisc_1(A_112,A_112)))
      | ~ v3_funct_2(B_113,A_112,A_112)
      | ~ v1_funct_2(B_113,A_112,A_112)
      | ~ v1_funct_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_390,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_384])).

tff(c_398,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_390])).

tff(c_418,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_398])).

tff(c_565,plain,(
    ! [F_134,A_132,C_133,D_131,E_136,B_135] :
      ( k1_partfun1(A_132,B_135,C_133,D_131,E_136,F_134) = k5_relat_1(E_136,F_134)
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(C_133,D_131)))
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_132,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2067,plain,(
    ! [E_188,A_185,B_189,A_186,B_187] :
      ( k1_partfun1(A_186,B_187,A_185,A_185,E_188,k2_funct_2(A_185,B_189)) = k5_relat_1(E_188,k2_funct_2(A_185,B_189))
      | ~ v1_funct_1(k2_funct_2(A_185,B_189))
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(E_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185)))
      | ~ v3_funct_2(B_189,A_185,A_185)
      | ~ v1_funct_2(B_189,A_185,A_185)
      | ~ v1_funct_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_30,c_565])).

tff(c_2087,plain,(
    ! [A_185,B_189] :
      ( k1_partfun1('#skF_2','#skF_2',A_185,A_185,'#skF_3',k2_funct_2(A_185,B_189)) = k5_relat_1('#skF_3',k2_funct_2(A_185,B_189))
      | ~ v1_funct_1(k2_funct_2(A_185,B_189))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185)))
      | ~ v3_funct_2(B_189,A_185,A_185)
      | ~ v1_funct_2(B_189,A_185,A_185)
      | ~ v1_funct_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_52,c_2067])).

tff(c_2136,plain,(
    ! [A_190,B_191] :
      ( k1_partfun1('#skF_2','#skF_2',A_190,A_190,'#skF_3',k2_funct_2(A_190,B_191)) = k5_relat_1('#skF_3',k2_funct_2(A_190,B_191))
      | ~ v1_funct_1(k2_funct_2(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2087])).

tff(c_2156,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2136])).

tff(c_2185,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_418,c_416,c_416,c_416,c_2156])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_419,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_74])).

tff(c_2187,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2185,c_419])).

tff(c_2194,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2187])).

tff(c_2197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58,c_298,c_336,c_354,c_2194])).

tff(c_2198,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2563,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2198])).

tff(c_3185,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3134,c_2563])).

tff(c_3192,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3185])).

tff(c_3195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2212,c_58,c_2441,c_2507,c_2359,c_3192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.30  
% 5.90/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.31  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.90/2.31  
% 5.90/2.31  %Foreground sorts:
% 5.90/2.31  
% 5.90/2.31  
% 5.90/2.31  %Background operators:
% 5.90/2.31  
% 5.90/2.31  
% 5.90/2.31  %Foreground operators:
% 5.90/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.90/2.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.90/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.90/2.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.90/2.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.90/2.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.90/2.31  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.90/2.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.90/2.31  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.90/2.31  tff('#skF_2', type, '#skF_2': $i).
% 5.90/2.31  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.90/2.31  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.31  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.90/2.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.90/2.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.90/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.31  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.90/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.90/2.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.90/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.90/2.31  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.90/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.31  
% 6.26/2.33  tff(f_144, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.26/2.33  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.26/2.33  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.26/2.33  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.26/2.33  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.26/2.33  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.26/2.33  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.26/2.33  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.26/2.33  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.26/2.33  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.26/2.33  tff(f_97, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.26/2.33  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.26/2.33  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.26/2.33  tff(f_131, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.26/2.33  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.26/2.33  tff(c_2200, plain, (![C_192, A_193, B_194]: (v1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.26/2.33  tff(c_2212, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2200])).
% 6.26/2.33  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.26/2.33  tff(c_54, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.26/2.33  tff(c_2427, plain, (![C_242, A_243, B_244]: (v2_funct_1(C_242) | ~v3_funct_2(C_242, A_243, B_244) | ~v1_funct_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.26/2.33  tff(c_2433, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2427])).
% 6.26/2.33  tff(c_2441, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2433])).
% 6.26/2.33  tff(c_40, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.26/2.33  tff(c_2489, plain, (![A_253, B_254, C_255, D_256]: (r2_relset_1(A_253, B_254, C_255, C_255) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))) | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.26/2.33  tff(c_2499, plain, (![A_257, C_258]: (r2_relset_1(A_257, A_257, C_258, C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_257, A_257))))), inference(resolution, [status(thm)], [c_40, c_2489])).
% 6.26/2.33  tff(c_2507, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_40, c_2499])).
% 6.26/2.33  tff(c_2232, plain, (![C_204, B_205, A_206]: (v5_relat_1(C_204, B_205) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.26/2.33  tff(c_2244, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_2232])).
% 6.26/2.33  tff(c_2249, plain, (![B_211, A_212]: (k2_relat_1(B_211)=A_212 | ~v2_funct_2(B_211, A_212) | ~v5_relat_1(B_211, A_212) | ~v1_relat_1(B_211))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.26/2.33  tff(c_2258, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2244, c_2249])).
% 6.26/2.33  tff(c_2267, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2212, c_2258])).
% 6.26/2.33  tff(c_2268, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2267])).
% 6.26/2.33  tff(c_2342, plain, (![C_228, B_229, A_230]: (v2_funct_2(C_228, B_229) | ~v3_funct_2(C_228, A_230, B_229) | ~v1_funct_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.26/2.33  tff(c_2348, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2342])).
% 6.26/2.33  tff(c_2356, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2348])).
% 6.26/2.33  tff(c_2358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2268, c_2356])).
% 6.26/2.33  tff(c_2359, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2267])).
% 6.26/2.33  tff(c_46, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.26/2.33  tff(c_6, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.26/2.33  tff(c_60, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 6.26/2.33  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.26/2.33  tff(c_2545, plain, (![A_271, B_272]: (k2_funct_2(A_271, B_272)=k2_funct_1(B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(k2_zfmisc_1(A_271, A_271))) | ~v3_funct_2(B_272, A_271, A_271) | ~v1_funct_2(B_272, A_271, A_271) | ~v1_funct_1(B_272))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.26/2.33  tff(c_2551, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2545])).
% 6.26/2.33  tff(c_2559, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2551])).
% 6.26/2.33  tff(c_2510, plain, (![A_259, B_260]: (v1_funct_1(k2_funct_2(A_259, B_260)) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.26/2.33  tff(c_2516, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2510])).
% 6.26/2.33  tff(c_2524, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2516])).
% 6.26/2.33  tff(c_2561, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2524])).
% 6.26/2.33  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(k2_funct_2(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v3_funct_2(B_23, A_22, A_22) | ~v1_funct_2(B_23, A_22, A_22) | ~v1_funct_1(B_23))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.26/2.33  tff(c_2715, plain, (![B_289, D_285, E_290, A_286, F_288, C_287]: (k1_partfun1(A_286, B_289, C_287, D_285, E_290, F_288)=k5_relat_1(E_290, F_288) | ~m1_subset_1(F_288, k1_zfmisc_1(k2_zfmisc_1(C_287, D_285))) | ~v1_funct_1(F_288) | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(A_286, B_289))) | ~v1_funct_1(E_290))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.26/2.33  tff(c_2723, plain, (![A_286, B_289, E_290]: (k1_partfun1(A_286, B_289, '#skF_2', '#skF_2', E_290, '#skF_3')=k5_relat_1(E_290, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(A_286, B_289))) | ~v1_funct_1(E_290))), inference(resolution, [status(thm)], [c_52, c_2715])).
% 6.26/2.33  tff(c_2740, plain, (![A_291, B_292, E_293]: (k1_partfun1(A_291, B_292, '#skF_2', '#skF_2', E_293, '#skF_3')=k5_relat_1(E_293, '#skF_3') | ~m1_subset_1(E_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_1(E_293))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2723])).
% 6.26/2.33  tff(c_3105, plain, (![A_307, B_308]: (k1_partfun1(A_307, A_307, '#skF_2', '#skF_2', k2_funct_2(A_307, B_308), '#skF_3')=k5_relat_1(k2_funct_2(A_307, B_308), '#skF_3') | ~v1_funct_1(k2_funct_2(A_307, B_308)) | ~m1_subset_1(B_308, k1_zfmisc_1(k2_zfmisc_1(A_307, A_307))) | ~v3_funct_2(B_308, A_307, A_307) | ~v1_funct_2(B_308, A_307, A_307) | ~v1_funct_1(B_308))), inference(resolution, [status(thm)], [c_30, c_2740])).
% 6.26/2.33  tff(c_3117, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3105])).
% 6.26/2.33  tff(c_3134, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2561, c_2559, c_2559, c_2559, c_3117])).
% 6.26/2.33  tff(c_75, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.26/2.33  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_75])).
% 6.26/2.33  tff(c_284, plain, (![C_88, A_89, B_90]: (v2_funct_1(C_88) | ~v3_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.26/2.33  tff(c_290, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_284])).
% 6.26/2.33  tff(c_298, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_290])).
% 6.26/2.33  tff(c_318, plain, (![A_96, B_97, C_98, D_99]: (r2_relset_1(A_96, B_97, C_98, C_98) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.26/2.33  tff(c_328, plain, (![A_100, C_101]: (r2_relset_1(A_100, A_100, C_101, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))))), inference(resolution, [status(thm)], [c_40, c_318])).
% 6.26/2.33  tff(c_336, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_40, c_328])).
% 6.26/2.33  tff(c_143, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.26/2.33  tff(c_155, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_143])).
% 6.26/2.33  tff(c_339, plain, (![A_102, B_103]: (k1_relset_1(A_102, A_102, B_103)=A_102 | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.26/2.33  tff(c_345, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_339])).
% 6.26/2.33  tff(c_354, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_155, c_345])).
% 6.26/2.33  tff(c_8, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.26/2.33  tff(c_59, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 6.26/2.33  tff(c_402, plain, (![A_117, B_118]: (k2_funct_2(A_117, B_118)=k2_funct_1(B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.26/2.33  tff(c_408, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_402])).
% 6.26/2.33  tff(c_416, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_408])).
% 6.26/2.33  tff(c_384, plain, (![A_112, B_113]: (v1_funct_1(k2_funct_2(A_112, B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_zfmisc_1(A_112, A_112))) | ~v3_funct_2(B_113, A_112, A_112) | ~v1_funct_2(B_113, A_112, A_112) | ~v1_funct_1(B_113))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.26/2.33  tff(c_390, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_384])).
% 6.26/2.33  tff(c_398, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_390])).
% 6.26/2.33  tff(c_418, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_398])).
% 6.26/2.33  tff(c_565, plain, (![F_134, A_132, C_133, D_131, E_136, B_135]: (k1_partfun1(A_132, B_135, C_133, D_131, E_136, F_134)=k5_relat_1(E_136, F_134) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(C_133, D_131))) | ~v1_funct_1(F_134) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_132, B_135))) | ~v1_funct_1(E_136))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.26/2.33  tff(c_2067, plain, (![E_188, A_185, B_189, A_186, B_187]: (k1_partfun1(A_186, B_187, A_185, A_185, E_188, k2_funct_2(A_185, B_189))=k5_relat_1(E_188, k2_funct_2(A_185, B_189)) | ~v1_funct_1(k2_funct_2(A_185, B_189)) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(E_188) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_185, A_185))) | ~v3_funct_2(B_189, A_185, A_185) | ~v1_funct_2(B_189, A_185, A_185) | ~v1_funct_1(B_189))), inference(resolution, [status(thm)], [c_30, c_565])).
% 6.26/2.33  tff(c_2087, plain, (![A_185, B_189]: (k1_partfun1('#skF_2', '#skF_2', A_185, A_185, '#skF_3', k2_funct_2(A_185, B_189))=k5_relat_1('#skF_3', k2_funct_2(A_185, B_189)) | ~v1_funct_1(k2_funct_2(A_185, B_189)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_185, A_185))) | ~v3_funct_2(B_189, A_185, A_185) | ~v1_funct_2(B_189, A_185, A_185) | ~v1_funct_1(B_189))), inference(resolution, [status(thm)], [c_52, c_2067])).
% 6.26/2.33  tff(c_2136, plain, (![A_190, B_191]: (k1_partfun1('#skF_2', '#skF_2', A_190, A_190, '#skF_3', k2_funct_2(A_190, B_191))=k5_relat_1('#skF_3', k2_funct_2(A_190, B_191)) | ~v1_funct_1(k2_funct_2(A_190, B_191)) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2087])).
% 6.26/2.33  tff(c_2156, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2136])).
% 6.26/2.33  tff(c_2185, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_418, c_416, c_416, c_416, c_2156])).
% 6.26/2.33  tff(c_50, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.26/2.33  tff(c_74, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 6.26/2.33  tff(c_419, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_74])).
% 6.26/2.33  tff(c_2187, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2185, c_419])).
% 6.26/2.33  tff(c_2194, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59, c_2187])).
% 6.26/2.33  tff(c_2197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_58, c_298, c_336, c_354, c_2194])).
% 6.26/2.33  tff(c_2198, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 6.26/2.33  tff(c_2563, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2198])).
% 6.26/2.33  tff(c_3185, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3134, c_2563])).
% 6.26/2.33  tff(c_3192, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3185])).
% 6.26/2.33  tff(c_3195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2212, c_58, c_2441, c_2507, c_2359, c_3192])).
% 6.26/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.33  
% 6.26/2.33  Inference rules
% 6.26/2.33  ----------------------
% 6.26/2.33  #Ref     : 0
% 6.26/2.33  #Sup     : 676
% 6.26/2.33  #Fact    : 0
% 6.26/2.33  #Define  : 0
% 6.26/2.33  #Split   : 3
% 6.26/2.33  #Chain   : 0
% 6.26/2.33  #Close   : 0
% 6.26/2.33  
% 6.26/2.33  Ordering : KBO
% 6.26/2.33  
% 6.26/2.33  Simplification rules
% 6.26/2.33  ----------------------
% 6.26/2.33  #Subsume      : 6
% 6.26/2.33  #Demod        : 1481
% 6.26/2.33  #Tautology    : 266
% 6.26/2.33  #SimpNegUnit  : 2
% 6.26/2.33  #BackRed      : 53
% 6.26/2.33  
% 6.26/2.33  #Partial instantiations: 0
% 6.26/2.33  #Strategies tried      : 1
% 6.26/2.33  
% 6.26/2.33  Timing (in seconds)
% 6.26/2.33  ----------------------
% 6.26/2.34  Preprocessing        : 0.34
% 6.26/2.34  Parsing              : 0.18
% 6.26/2.34  CNF conversion       : 0.02
% 6.26/2.34  Main loop            : 1.19
% 6.26/2.34  Inferencing          : 0.41
% 6.26/2.34  Reduction            : 0.45
% 6.26/2.34  Demodulation         : 0.34
% 6.26/2.34  BG Simplification    : 0.04
% 6.26/2.34  Subsumption          : 0.19
% 6.26/2.34  Abstraction          : 0.05
% 6.26/2.34  MUC search           : 0.00
% 6.26/2.34  Cooper               : 0.00
% 6.26/2.34  Total                : 1.58
% 6.26/2.34  Index Insertion      : 0.00
% 6.26/2.34  Index Deletion       : 0.00
% 6.26/2.34  Index Matching       : 0.00
% 6.26/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
