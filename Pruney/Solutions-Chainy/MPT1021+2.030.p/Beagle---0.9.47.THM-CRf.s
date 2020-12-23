%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:04 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 346 expanded)
%              Number of leaves         :   42 ( 150 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 (1059 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(f_141,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_94,axiom,(
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

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_71,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2413,plain,(
    ! [C_231,A_232,B_233] :
      ( v2_funct_1(C_231)
      | ~ v3_funct_2(C_231,A_232,B_233)
      | ~ v1_funct_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2419,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2413])).

tff(c_2427,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2419])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2485,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( r2_relset_1(A_246,B_247,C_248,C_248)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2495,plain,(
    ! [A_250,C_251] :
      ( r2_relset_1(A_250,A_250,C_251,C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_250,A_250))) ) ),
    inference(resolution,[status(thm)],[c_38,c_2485])).

tff(c_2503,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_38,c_2495])).

tff(c_2229,plain,(
    ! [C_199,B_200,A_201] :
      ( v5_relat_1(C_199,B_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2241,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2229])).

tff(c_2246,plain,(
    ! [B_206,A_207] :
      ( k2_relat_1(B_206) = A_207
      | ~ v2_funct_2(B_206,A_207)
      | ~ v5_relat_1(B_206,A_207)
      | ~ v1_relat_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2255,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2241,c_2246])).

tff(c_2264,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2255])).

tff(c_2265,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2264])).

tff(c_2338,plain,(
    ! [C_221,B_222,A_223] :
      ( v2_funct_2(C_221,B_222)
      | ~ v3_funct_2(C_221,A_223,B_222)
      | ~ v1_funct_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2344,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2338])).

tff(c_2352,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2344])).

tff(c_2354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2265,c_2352])).

tff(c_2355,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2264])).

tff(c_44,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2536,plain,(
    ! [A_258,B_259] :
      ( k2_funct_2(A_258,B_259) = k2_funct_1(B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258)))
      | ~ v3_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2542,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2536])).

tff(c_2550,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2542])).

tff(c_2507,plain,(
    ! [A_253,B_254] :
      ( v1_funct_1(k2_funct_2(A_253,B_254))
      | ~ m1_subset_1(B_254,k1_zfmisc_1(k2_zfmisc_1(A_253,A_253)))
      | ~ v3_funct_2(B_254,A_253,A_253)
      | ~ v1_funct_2(B_254,A_253,A_253)
      | ~ v1_funct_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2513,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2507])).

tff(c_2521,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2513])).

tff(c_2552,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2550,c_2521])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_funct_2(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v3_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2713,plain,(
    ! [C_277,B_279,A_276,D_275,E_280,F_278] :
      ( k1_partfun1(A_276,B_279,C_277,D_275,E_280,F_278) = k5_relat_1(E_280,F_278)
      | ~ m1_subset_1(F_278,k1_zfmisc_1(k2_zfmisc_1(C_277,D_275)))
      | ~ v1_funct_1(F_278)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_276,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2721,plain,(
    ! [A_276,B_279,E_280] :
      ( k1_partfun1(A_276,B_279,'#skF_2','#skF_2',E_280,'#skF_3') = k5_relat_1(E_280,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_276,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(resolution,[status(thm)],[c_50,c_2713])).

tff(c_2745,plain,(
    ! [A_281,B_282,E_283] :
      ( k1_partfun1(A_281,B_282,'#skF_2','#skF_2',E_283,'#skF_3') = k5_relat_1(E_283,'#skF_3')
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(E_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2721])).

tff(c_3107,plain,(
    ! [A_295,B_296] :
      ( k1_partfun1(A_295,A_295,'#skF_2','#skF_2',k2_funct_2(A_295,B_296),'#skF_3') = k5_relat_1(k2_funct_2(A_295,B_296),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_295,B_296))
      | ~ m1_subset_1(B_296,k1_zfmisc_1(k2_zfmisc_1(A_295,A_295)))
      | ~ v3_funct_2(B_296,A_295,A_295)
      | ~ v1_funct_2(B_296,A_295,A_295)
      | ~ v1_funct_1(B_296) ) ),
    inference(resolution,[status(thm)],[c_28,c_2745])).

tff(c_3119,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3107])).

tff(c_3136,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2552,c_2550,c_2550,c_2550,c_3119])).

tff(c_279,plain,(
    ! [C_82,A_83,B_84] :
      ( v2_funct_1(C_82)
      | ~ v3_funct_2(C_82,A_83,B_84)
      | ~ v1_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_285,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_279])).

tff(c_293,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_285])).

tff(c_350,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( r2_relset_1(A_96,B_97,C_98,C_98)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_360,plain,(
    ! [A_100,C_101] :
      ( r2_relset_1(A_100,A_100,C_101,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100))) ) ),
    inference(resolution,[status(thm)],[c_38,c_350])).

tff(c_368,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_38,c_360])).

tff(c_233,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_245,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_233])).

tff(c_323,plain,(
    ! [A_94,B_95] :
      ( k1_relset_1(A_94,A_94,B_95) = A_94
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(A_94,A_94)))
      | ~ v1_funct_2(B_95,A_94,A_94)
      | ~ v1_funct_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_329,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_323])).

tff(c_338,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_245,c_329])).

tff(c_6,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_405,plain,(
    ! [A_112,B_113] :
      ( k2_funct_2(A_112,B_113) = k2_funct_1(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_zfmisc_1(A_112,A_112)))
      | ~ v3_funct_2(B_113,A_112,A_112)
      | ~ v1_funct_2(B_113,A_112,A_112)
      | ~ v1_funct_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_411,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_405])).

tff(c_419,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_411])).

tff(c_389,plain,(
    ! [A_110,B_111] :
      ( v1_funct_1(k2_funct_2(A_110,B_111))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v3_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_395,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_389])).

tff(c_403,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_395])).

tff(c_421,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_403])).

tff(c_570,plain,(
    ! [B_133,A_130,E_134,D_129,F_132,C_131] :
      ( k1_partfun1(A_130,B_133,C_131,D_129,E_134,F_132) = k5_relat_1(E_134,F_132)
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_131,D_129)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_130,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2094,plain,(
    ! [E_184,B_185,A_182,B_186,A_183] :
      ( k1_partfun1(A_182,B_185,A_183,A_183,E_184,k2_funct_2(A_183,B_186)) = k5_relat_1(E_184,k2_funct_2(A_183,B_186))
      | ~ v1_funct_1(k2_funct_2(A_183,B_186))
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_185)))
      | ~ v1_funct_1(E_184)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_186,A_183,A_183)
      | ~ v1_funct_2(B_186,A_183,A_183)
      | ~ v1_funct_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_28,c_570])).

tff(c_2114,plain,(
    ! [A_183,B_186] :
      ( k1_partfun1('#skF_2','#skF_2',A_183,A_183,'#skF_3',k2_funct_2(A_183,B_186)) = k5_relat_1('#skF_3',k2_funct_2(A_183,B_186))
      | ~ v1_funct_1(k2_funct_2(A_183,B_186))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v3_funct_2(B_186,A_183,A_183)
      | ~ v1_funct_2(B_186,A_183,A_183)
      | ~ v1_funct_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_50,c_2094])).

tff(c_2147,plain,(
    ! [A_188,B_189] :
      ( k1_partfun1('#skF_2','#skF_2',A_188,A_188,'#skF_3',k2_funct_2(A_188,B_189)) = k5_relat_1('#skF_3',k2_funct_2(A_188,B_189))
      | ~ v1_funct_1(k2_funct_2(A_188,B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_1(B_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2114])).

tff(c_2167,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2147])).

tff(c_2196,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_421,c_419,c_419,c_419,c_2167])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_422,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_85])).

tff(c_2198,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_422])).

tff(c_2205,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2198])).

tff(c_2208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_293,c_368,c_338,c_2205])).

tff(c_2209,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2554,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2550,c_2209])).

tff(c_3165,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3136,c_2554])).

tff(c_3172,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_3165])).

tff(c_3175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_2427,c_2503,c_2355,c_3172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:27:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.05/2.19  
% 6.05/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.05/2.19  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 6.05/2.19  
% 6.05/2.19  %Foreground sorts:
% 6.05/2.19  
% 6.05/2.19  
% 6.05/2.19  %Background operators:
% 6.05/2.19  
% 6.05/2.19  
% 6.05/2.19  %Foreground operators:
% 6.05/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.05/2.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.05/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.05/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.05/2.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.05/2.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.05/2.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.05/2.19  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.05/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.05/2.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.05/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.05/2.19  tff('#skF_2', type, '#skF_2': $i).
% 6.05/2.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.05/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.05/2.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.05/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.05/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.05/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.05/2.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.05/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.05/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.05/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.05/2.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.05/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.05/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.05/2.19  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.05/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.05/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.05/2.19  
% 6.05/2.22  tff(f_141, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.05/2.22  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.05/2.22  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.05/2.22  tff(f_98, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.05/2.22  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.05/2.22  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.05/2.22  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.05/2.22  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.05/2.22  tff(f_38, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.05/2.22  tff(f_118, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.05/2.22  tff(f_94, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.05/2.22  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.05/2.22  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.05/2.22  tff(f_128, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.05/2.22  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.05/2.22  tff(c_71, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.05/2.22  tff(c_83, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_71])).
% 6.05/2.22  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.05/2.22  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.05/2.22  tff(c_2413, plain, (![C_231, A_232, B_233]: (v2_funct_1(C_231) | ~v3_funct_2(C_231, A_232, B_233) | ~v1_funct_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.05/2.22  tff(c_2419, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2413])).
% 6.05/2.22  tff(c_2427, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2419])).
% 6.05/2.22  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.05/2.22  tff(c_2485, plain, (![A_246, B_247, C_248, D_249]: (r2_relset_1(A_246, B_247, C_248, C_248) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.05/2.22  tff(c_2495, plain, (![A_250, C_251]: (r2_relset_1(A_250, A_250, C_251, C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_250, A_250))))), inference(resolution, [status(thm)], [c_38, c_2485])).
% 6.05/2.22  tff(c_2503, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_38, c_2495])).
% 6.05/2.22  tff(c_2229, plain, (![C_199, B_200, A_201]: (v5_relat_1(C_199, B_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.05/2.22  tff(c_2241, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_2229])).
% 6.05/2.22  tff(c_2246, plain, (![B_206, A_207]: (k2_relat_1(B_206)=A_207 | ~v2_funct_2(B_206, A_207) | ~v5_relat_1(B_206, A_207) | ~v1_relat_1(B_206))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.05/2.22  tff(c_2255, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2241, c_2246])).
% 6.05/2.22  tff(c_2264, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2255])).
% 6.05/2.22  tff(c_2265, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2264])).
% 6.05/2.22  tff(c_2338, plain, (![C_221, B_222, A_223]: (v2_funct_2(C_221, B_222) | ~v3_funct_2(C_221, A_223, B_222) | ~v1_funct_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.05/2.22  tff(c_2344, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2338])).
% 6.05/2.22  tff(c_2352, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2344])).
% 6.05/2.22  tff(c_2354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2265, c_2352])).
% 6.05/2.22  tff(c_2355, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2264])).
% 6.05/2.22  tff(c_44, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.05/2.22  tff(c_4, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.05/2.22  tff(c_58, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 6.05/2.22  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.05/2.22  tff(c_2536, plain, (![A_258, B_259]: (k2_funct_2(A_258, B_259)=k2_funct_1(B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))) | ~v3_funct_2(B_259, A_258, A_258) | ~v1_funct_2(B_259, A_258, A_258) | ~v1_funct_1(B_259))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.05/2.22  tff(c_2542, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2536])).
% 6.05/2.22  tff(c_2550, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2542])).
% 6.05/2.22  tff(c_2507, plain, (![A_253, B_254]: (v1_funct_1(k2_funct_2(A_253, B_254)) | ~m1_subset_1(B_254, k1_zfmisc_1(k2_zfmisc_1(A_253, A_253))) | ~v3_funct_2(B_254, A_253, A_253) | ~v1_funct_2(B_254, A_253, A_253) | ~v1_funct_1(B_254))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.05/2.22  tff(c_2513, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2507])).
% 6.05/2.22  tff(c_2521, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2513])).
% 6.05/2.22  tff(c_2552, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2550, c_2521])).
% 6.05/2.22  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(k2_funct_2(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v3_funct_2(B_23, A_22, A_22) | ~v1_funct_2(B_23, A_22, A_22) | ~v1_funct_1(B_23))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.05/2.22  tff(c_2713, plain, (![C_277, B_279, A_276, D_275, E_280, F_278]: (k1_partfun1(A_276, B_279, C_277, D_275, E_280, F_278)=k5_relat_1(E_280, F_278) | ~m1_subset_1(F_278, k1_zfmisc_1(k2_zfmisc_1(C_277, D_275))) | ~v1_funct_1(F_278) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_276, B_279))) | ~v1_funct_1(E_280))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.05/2.22  tff(c_2721, plain, (![A_276, B_279, E_280]: (k1_partfun1(A_276, B_279, '#skF_2', '#skF_2', E_280, '#skF_3')=k5_relat_1(E_280, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_276, B_279))) | ~v1_funct_1(E_280))), inference(resolution, [status(thm)], [c_50, c_2713])).
% 6.05/2.22  tff(c_2745, plain, (![A_281, B_282, E_283]: (k1_partfun1(A_281, B_282, '#skF_2', '#skF_2', E_283, '#skF_3')=k5_relat_1(E_283, '#skF_3') | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(E_283))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2721])).
% 6.05/2.22  tff(c_3107, plain, (![A_295, B_296]: (k1_partfun1(A_295, A_295, '#skF_2', '#skF_2', k2_funct_2(A_295, B_296), '#skF_3')=k5_relat_1(k2_funct_2(A_295, B_296), '#skF_3') | ~v1_funct_1(k2_funct_2(A_295, B_296)) | ~m1_subset_1(B_296, k1_zfmisc_1(k2_zfmisc_1(A_295, A_295))) | ~v3_funct_2(B_296, A_295, A_295) | ~v1_funct_2(B_296, A_295, A_295) | ~v1_funct_1(B_296))), inference(resolution, [status(thm)], [c_28, c_2745])).
% 6.05/2.22  tff(c_3119, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3107])).
% 6.05/2.22  tff(c_3136, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2552, c_2550, c_2550, c_2550, c_3119])).
% 6.05/2.22  tff(c_279, plain, (![C_82, A_83, B_84]: (v2_funct_1(C_82) | ~v3_funct_2(C_82, A_83, B_84) | ~v1_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.05/2.22  tff(c_285, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_279])).
% 6.05/2.22  tff(c_293, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_285])).
% 6.05/2.22  tff(c_350, plain, (![A_96, B_97, C_98, D_99]: (r2_relset_1(A_96, B_97, C_98, C_98) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.05/2.22  tff(c_360, plain, (![A_100, C_101]: (r2_relset_1(A_100, A_100, C_101, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))))), inference(resolution, [status(thm)], [c_38, c_350])).
% 6.05/2.22  tff(c_368, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_38, c_360])).
% 6.05/2.22  tff(c_233, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.05/2.22  tff(c_245, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_233])).
% 6.05/2.22  tff(c_323, plain, (![A_94, B_95]: (k1_relset_1(A_94, A_94, B_95)=A_94 | ~m1_subset_1(B_95, k1_zfmisc_1(k2_zfmisc_1(A_94, A_94))) | ~v1_funct_2(B_95, A_94, A_94) | ~v1_funct_1(B_95))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.05/2.22  tff(c_329, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_323])).
% 6.05/2.22  tff(c_338, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_245, c_329])).
% 6.05/2.22  tff(c_6, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.05/2.22  tff(c_57, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 6.05/2.22  tff(c_405, plain, (![A_112, B_113]: (k2_funct_2(A_112, B_113)=k2_funct_1(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_zfmisc_1(A_112, A_112))) | ~v3_funct_2(B_113, A_112, A_112) | ~v1_funct_2(B_113, A_112, A_112) | ~v1_funct_1(B_113))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.05/2.22  tff(c_411, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_405])).
% 6.05/2.22  tff(c_419, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_411])).
% 6.05/2.22  tff(c_389, plain, (![A_110, B_111]: (v1_funct_1(k2_funct_2(A_110, B_111)) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v3_funct_2(B_111, A_110, A_110) | ~v1_funct_2(B_111, A_110, A_110) | ~v1_funct_1(B_111))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.05/2.22  tff(c_395, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_389])).
% 6.05/2.22  tff(c_403, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_395])).
% 6.05/2.22  tff(c_421, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_403])).
% 6.05/2.22  tff(c_570, plain, (![B_133, A_130, E_134, D_129, F_132, C_131]: (k1_partfun1(A_130, B_133, C_131, D_129, E_134, F_132)=k5_relat_1(E_134, F_132) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_131, D_129))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_130, B_133))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.05/2.22  tff(c_2094, plain, (![E_184, B_185, A_182, B_186, A_183]: (k1_partfun1(A_182, B_185, A_183, A_183, E_184, k2_funct_2(A_183, B_186))=k5_relat_1(E_184, k2_funct_2(A_183, B_186)) | ~v1_funct_1(k2_funct_2(A_183, B_186)) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_185))) | ~v1_funct_1(E_184) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_186, A_183, A_183) | ~v1_funct_2(B_186, A_183, A_183) | ~v1_funct_1(B_186))), inference(resolution, [status(thm)], [c_28, c_570])).
% 6.05/2.22  tff(c_2114, plain, (![A_183, B_186]: (k1_partfun1('#skF_2', '#skF_2', A_183, A_183, '#skF_3', k2_funct_2(A_183, B_186))=k5_relat_1('#skF_3', k2_funct_2(A_183, B_186)) | ~v1_funct_1(k2_funct_2(A_183, B_186)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_183, A_183))) | ~v3_funct_2(B_186, A_183, A_183) | ~v1_funct_2(B_186, A_183, A_183) | ~v1_funct_1(B_186))), inference(resolution, [status(thm)], [c_50, c_2094])).
% 6.05/2.22  tff(c_2147, plain, (![A_188, B_189]: (k1_partfun1('#skF_2', '#skF_2', A_188, A_188, '#skF_3', k2_funct_2(A_188, B_189))=k5_relat_1('#skF_3', k2_funct_2(A_188, B_189)) | ~v1_funct_1(k2_funct_2(A_188, B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_189, A_188, A_188) | ~v1_funct_2(B_189, A_188, A_188) | ~v1_funct_1(B_189))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2114])).
% 6.05/2.22  tff(c_2167, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2147])).
% 6.05/2.22  tff(c_2196, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_421, c_419, c_419, c_419, c_2167])).
% 6.05/2.22  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 6.05/2.22  tff(c_85, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 6.05/2.22  tff(c_422, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_85])).
% 6.05/2.22  tff(c_2198, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_422])).
% 6.05/2.22  tff(c_2205, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_57, c_2198])).
% 6.05/2.22  tff(c_2208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_293, c_368, c_338, c_2205])).
% 6.05/2.22  tff(c_2209, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 6.05/2.22  tff(c_2554, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2550, c_2209])).
% 6.05/2.22  tff(c_3165, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3136, c_2554])).
% 6.05/2.22  tff(c_3172, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_3165])).
% 6.05/2.22  tff(c_3175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_2427, c_2503, c_2355, c_3172])).
% 6.05/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.05/2.22  
% 6.05/2.22  Inference rules
% 6.05/2.22  ----------------------
% 6.05/2.22  #Ref     : 0
% 6.05/2.22  #Sup     : 670
% 6.05/2.22  #Fact    : 0
% 6.05/2.22  #Define  : 0
% 6.05/2.22  #Split   : 3
% 6.05/2.22  #Chain   : 0
% 6.05/2.22  #Close   : 0
% 6.05/2.22  
% 6.05/2.22  Ordering : KBO
% 6.05/2.22  
% 6.05/2.22  Simplification rules
% 6.05/2.22  ----------------------
% 6.05/2.22  #Subsume      : 6
% 6.05/2.22  #Demod        : 1482
% 6.05/2.22  #Tautology    : 260
% 6.05/2.22  #SimpNegUnit  : 2
% 6.05/2.22  #BackRed      : 61
% 6.05/2.22  
% 6.05/2.22  #Partial instantiations: 0
% 6.05/2.22  #Strategies tried      : 1
% 6.05/2.22  
% 6.05/2.22  Timing (in seconds)
% 6.05/2.22  ----------------------
% 6.05/2.22  Preprocessing        : 0.34
% 6.05/2.22  Parsing              : 0.18
% 6.05/2.22  CNF conversion       : 0.02
% 6.05/2.22  Main loop            : 1.11
% 6.05/2.22  Inferencing          : 0.37
% 6.05/2.22  Reduction            : 0.43
% 6.05/2.22  Demodulation         : 0.33
% 6.05/2.22  BG Simplification    : 0.04
% 6.05/2.22  Subsumption          : 0.19
% 6.05/2.22  Abstraction          : 0.05
% 6.05/2.22  MUC search           : 0.00
% 6.05/2.22  Cooper               : 0.00
% 6.05/2.22  Total                : 1.50
% 6.05/2.22  Index Insertion      : 0.00
% 6.05/2.22  Index Deletion       : 0.00
% 6.05/2.22  Index Matching       : 0.00
% 6.05/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
