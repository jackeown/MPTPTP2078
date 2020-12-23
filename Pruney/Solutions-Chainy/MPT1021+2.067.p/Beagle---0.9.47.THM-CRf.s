%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:10 EST 2020

% Result     : Theorem 9.15s
% Output     : CNFRefutation 9.15s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 358 expanded)
%              Number of leaves         :   43 ( 154 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 (1083 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_124,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_98,axiom,(
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

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2208,plain,(
    ! [B_190,A_191] :
      ( v1_relat_1(B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_191))
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2214,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_2208])).

tff(c_2223,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2214])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2433,plain,(
    ! [C_233,A_234,B_235] :
      ( v2_funct_1(C_233)
      | ~ v3_funct_2(C_233,A_234,B_235)
      | ~ v1_funct_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2439,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2433])).

tff(c_2447,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2439])).

tff(c_40,plain,(
    ! [A_25] : m1_subset_1(k6_partfun1(A_25),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2466,plain,(
    ! [A_240,B_241,C_242,D_243] :
      ( r2_relset_1(A_240,B_241,C_242,C_242)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2476,plain,(
    ! [A_244,C_245] :
      ( r2_relset_1(A_244,A_244,C_245,C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_244,A_244))) ) ),
    inference(resolution,[status(thm)],[c_40,c_2466])).

tff(c_2484,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_40,c_2476])).

tff(c_2243,plain,(
    ! [C_200,B_201,A_202] :
      ( v5_relat_1(C_200,B_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2255,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2243])).

tff(c_2260,plain,(
    ! [B_207,A_208] :
      ( k2_relat_1(B_207) = A_208
      | ~ v2_funct_2(B_207,A_208)
      | ~ v5_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2269,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2255,c_2260])).

tff(c_2276,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2223,c_2269])).

tff(c_2277,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2276])).

tff(c_2349,plain,(
    ! [C_221,B_222,A_223] :
      ( v2_funct_2(C_221,B_222)
      | ~ v3_funct_2(C_221,A_223,B_222)
      | ~ v1_funct_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2355,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2349])).

tff(c_2363,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2355])).

tff(c_2365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2277,c_2363])).

tff(c_2366,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2276])).

tff(c_46,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2548,plain,(
    ! [A_258,B_259] :
      ( k2_funct_2(A_258,B_259) = k2_funct_1(B_259)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258)))
      | ~ v3_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_2(B_259,A_258,A_258)
      | ~ v1_funct_1(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2554,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2548])).

tff(c_2562,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2554])).

tff(c_2523,plain,(
    ! [A_256,B_257] :
      ( v1_funct_1(k2_funct_2(A_256,B_257))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_zfmisc_1(A_256,A_256)))
      | ~ v3_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2529,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2523])).

tff(c_2537,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2529])).

tff(c_2564,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2537])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_funct_2(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2738,plain,(
    ! [E_281,A_278,F_279,B_277,D_276,C_280] :
      ( k1_partfun1(A_278,B_277,C_280,D_276,E_281,F_279) = k5_relat_1(E_281,F_279)
      | ~ m1_subset_1(F_279,k1_zfmisc_1(k2_zfmisc_1(C_280,D_276)))
      | ~ v1_funct_1(F_279)
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_278,B_277)))
      | ~ v1_funct_1(E_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2746,plain,(
    ! [A_278,B_277,E_281] :
      ( k1_partfun1(A_278,B_277,'#skF_1','#skF_1',E_281,'#skF_2') = k5_relat_1(E_281,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_278,B_277)))
      | ~ v1_funct_1(E_281) ) ),
    inference(resolution,[status(thm)],[c_52,c_2738])).

tff(c_2760,plain,(
    ! [A_282,B_283,E_284] :
      ( k1_partfun1(A_282,B_283,'#skF_1','#skF_1',E_284,'#skF_2') = k5_relat_1(E_284,'#skF_2')
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(E_284) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2746])).

tff(c_3082,plain,(
    ! [A_294,B_295] :
      ( k1_partfun1(A_294,A_294,'#skF_1','#skF_1',k2_funct_2(A_294,B_295),'#skF_2') = k5_relat_1(k2_funct_2(A_294,B_295),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_294,B_295))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(k2_zfmisc_1(A_294,A_294)))
      | ~ v3_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_1(B_295) ) ),
    inference(resolution,[status(thm)],[c_30,c_2760])).

tff(c_3094,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_3082])).

tff(c_3111,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2564,c_2562,c_2562,c_2562,c_3094])).

tff(c_75,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_90,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_283,plain,(
    ! [C_84,A_85,B_86] :
      ( v2_funct_1(C_84)
      | ~ v3_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_289,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_283])).

tff(c_297,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_289])).

tff(c_345,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r2_relset_1(A_95,B_96,C_97,C_97)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_355,plain,(
    ! [A_99,C_100] :
      ( r2_relset_1(A_99,A_99,C_100,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99))) ) ),
    inference(resolution,[status(thm)],[c_40,c_345])).

tff(c_363,plain,(
    ! [A_25] : r2_relset_1(A_25,A_25,k6_partfun1(A_25),k6_partfun1(A_25)) ),
    inference(resolution,[status(thm)],[c_40,c_355])).

tff(c_144,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_156,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_144])).

tff(c_317,plain,(
    ! [A_92,B_93] :
      ( k1_relset_1(A_92,A_92,B_93) = A_92
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_323,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_317])).

tff(c_332,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_156,c_323])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_403,plain,(
    ! [A_117,B_118] :
      ( k2_funct_2(A_117,B_118) = k2_funct_1(B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_409,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_403])).

tff(c_417,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_409])).

tff(c_385,plain,(
    ! [A_112,B_113] :
      ( v1_funct_1(k2_funct_2(A_112,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_zfmisc_1(A_112,A_112)))
      | ~ v3_funct_2(B_113,A_112,A_112)
      | ~ v1_funct_2(B_113,A_112,A_112)
      | ~ v1_funct_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_391,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_385])).

tff(c_399,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_391])).

tff(c_419,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_399])).

tff(c_569,plain,(
    ! [C_133,E_134,A_131,D_129,F_132,B_130] :
      ( k1_partfun1(A_131,B_130,C_133,D_129,E_134,F_132) = k5_relat_1(E_134,F_132)
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_133,D_129)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2079,plain,(
    ! [E_185,A_187,B_186,A_183,B_184] :
      ( k1_partfun1(A_183,B_184,A_187,A_187,E_185,k2_funct_2(A_187,B_186)) = k5_relat_1(E_185,k2_funct_2(A_187,B_186))
      | ~ v1_funct_1(k2_funct_2(A_187,B_186))
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_186,A_187,A_187)
      | ~ v1_funct_2(B_186,A_187,A_187)
      | ~ v1_funct_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_30,c_569])).

tff(c_2099,plain,(
    ! [A_187,B_186] :
      ( k1_partfun1('#skF_1','#skF_1',A_187,A_187,'#skF_2',k2_funct_2(A_187,B_186)) = k5_relat_1('#skF_2',k2_funct_2(A_187,B_186))
      | ~ v1_funct_1(k2_funct_2(A_187,B_186))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_186,A_187,A_187)
      | ~ v1_funct_2(B_186,A_187,A_187)
      | ~ v1_funct_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_52,c_2079])).

tff(c_2144,plain,(
    ! [A_188,B_189] :
      ( k1_partfun1('#skF_1','#skF_1',A_188,A_188,'#skF_2',k2_funct_2(A_188,B_189)) = k5_relat_1('#skF_2',k2_funct_2(A_188,B_189))
      | ~ v1_funct_1(k2_funct_2(A_188,B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_1(B_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2099])).

tff(c_2164,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2144])).

tff(c_2193,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_419,c_417,c_417,c_417,c_2164])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_420,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_74])).

tff(c_2195,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2193,c_420])).

tff(c_2202,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2195])).

tff(c_2205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_58,c_297,c_363,c_332,c_2202])).

tff(c_2206,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2566,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2206])).

tff(c_3176,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3111,c_2566])).

tff(c_3183,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3176])).

tff(c_3186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2223,c_58,c_2447,c_2484,c_2366,c_3183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.15/3.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.32  
% 9.15/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.33  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.15/3.33  
% 9.15/3.33  %Foreground sorts:
% 9.15/3.33  
% 9.15/3.33  
% 9.15/3.33  %Background operators:
% 9.15/3.33  
% 9.15/3.33  
% 9.15/3.33  %Foreground operators:
% 9.15/3.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.15/3.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.15/3.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.15/3.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.15/3.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.15/3.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.15/3.33  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 9.15/3.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.15/3.33  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.15/3.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.15/3.33  tff('#skF_2', type, '#skF_2': $i).
% 9.15/3.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.15/3.33  tff('#skF_1', type, '#skF_1': $i).
% 9.15/3.33  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.15/3.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.15/3.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.15/3.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.15/3.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.15/3.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.15/3.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.15/3.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.15/3.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.15/3.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.15/3.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.15/3.33  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 9.15/3.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.15/3.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.15/3.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.15/3.33  
% 9.15/3.36  tff(f_36, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.15/3.36  tff(f_145, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 9.15/3.36  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.15/3.36  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 9.15/3.36  tff(f_102, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.15/3.36  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 9.15/3.36  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.15/3.36  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.15/3.36  tff(f_124, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.15/3.36  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.15/3.36  tff(f_122, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 9.15/3.36  tff(f_98, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 9.15/3.36  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.15/3.36  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.15/3.36  tff(f_132, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 9.15/3.36  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.15/3.36  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.15/3.36  tff(c_2208, plain, (![B_190, A_191]: (v1_relat_1(B_190) | ~m1_subset_1(B_190, k1_zfmisc_1(A_191)) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.15/3.36  tff(c_2214, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_2208])).
% 9.15/3.36  tff(c_2223, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2214])).
% 9.15/3.36  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.15/3.36  tff(c_54, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.15/3.36  tff(c_2433, plain, (![C_233, A_234, B_235]: (v2_funct_1(C_233) | ~v3_funct_2(C_233, A_234, B_235) | ~v1_funct_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.15/3.36  tff(c_2439, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2433])).
% 9.15/3.36  tff(c_2447, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2439])).
% 9.15/3.36  tff(c_40, plain, (![A_25]: (m1_subset_1(k6_partfun1(A_25), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.15/3.36  tff(c_2466, plain, (![A_240, B_241, C_242, D_243]: (r2_relset_1(A_240, B_241, C_242, C_242) | ~m1_subset_1(D_243, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.15/3.36  tff(c_2476, plain, (![A_244, C_245]: (r2_relset_1(A_244, A_244, C_245, C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_244, A_244))))), inference(resolution, [status(thm)], [c_40, c_2466])).
% 9.15/3.36  tff(c_2484, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_40, c_2476])).
% 9.15/3.36  tff(c_2243, plain, (![C_200, B_201, A_202]: (v5_relat_1(C_200, B_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.15/3.36  tff(c_2255, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_2243])).
% 9.15/3.36  tff(c_2260, plain, (![B_207, A_208]: (k2_relat_1(B_207)=A_208 | ~v2_funct_2(B_207, A_208) | ~v5_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.15/3.36  tff(c_2269, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2255, c_2260])).
% 9.15/3.36  tff(c_2276, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2223, c_2269])).
% 9.15/3.36  tff(c_2277, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2276])).
% 9.15/3.36  tff(c_2349, plain, (![C_221, B_222, A_223]: (v2_funct_2(C_221, B_222) | ~v3_funct_2(C_221, A_223, B_222) | ~v1_funct_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.15/3.36  tff(c_2355, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2349])).
% 9.15/3.36  tff(c_2363, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2355])).
% 9.15/3.36  tff(c_2365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2277, c_2363])).
% 9.15/3.36  tff(c_2366, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2276])).
% 9.15/3.36  tff(c_46, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.15/3.36  tff(c_8, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.15/3.36  tff(c_60, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 9.15/3.36  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.15/3.36  tff(c_2548, plain, (![A_258, B_259]: (k2_funct_2(A_258, B_259)=k2_funct_1(B_259) | ~m1_subset_1(B_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))) | ~v3_funct_2(B_259, A_258, A_258) | ~v1_funct_2(B_259, A_258, A_258) | ~v1_funct_1(B_259))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.15/3.36  tff(c_2554, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2548])).
% 9.15/3.36  tff(c_2562, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2554])).
% 9.15/3.36  tff(c_2523, plain, (![A_256, B_257]: (v1_funct_1(k2_funct_2(A_256, B_257)) | ~m1_subset_1(B_257, k1_zfmisc_1(k2_zfmisc_1(A_256, A_256))) | ~v3_funct_2(B_257, A_256, A_256) | ~v1_funct_2(B_257, A_256, A_256) | ~v1_funct_1(B_257))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.15/3.36  tff(c_2529, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2523])).
% 9.15/3.36  tff(c_2537, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2529])).
% 9.15/3.36  tff(c_2564, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2537])).
% 9.15/3.36  tff(c_30, plain, (![A_23, B_24]: (m1_subset_1(k2_funct_2(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.15/3.36  tff(c_2738, plain, (![E_281, A_278, F_279, B_277, D_276, C_280]: (k1_partfun1(A_278, B_277, C_280, D_276, E_281, F_279)=k5_relat_1(E_281, F_279) | ~m1_subset_1(F_279, k1_zfmisc_1(k2_zfmisc_1(C_280, D_276))) | ~v1_funct_1(F_279) | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_278, B_277))) | ~v1_funct_1(E_281))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.15/3.36  tff(c_2746, plain, (![A_278, B_277, E_281]: (k1_partfun1(A_278, B_277, '#skF_1', '#skF_1', E_281, '#skF_2')=k5_relat_1(E_281, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_278, B_277))) | ~v1_funct_1(E_281))), inference(resolution, [status(thm)], [c_52, c_2738])).
% 9.15/3.36  tff(c_2760, plain, (![A_282, B_283, E_284]: (k1_partfun1(A_282, B_283, '#skF_1', '#skF_1', E_284, '#skF_2')=k5_relat_1(E_284, '#skF_2') | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(E_284))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2746])).
% 9.15/3.36  tff(c_3082, plain, (![A_294, B_295]: (k1_partfun1(A_294, A_294, '#skF_1', '#skF_1', k2_funct_2(A_294, B_295), '#skF_2')=k5_relat_1(k2_funct_2(A_294, B_295), '#skF_2') | ~v1_funct_1(k2_funct_2(A_294, B_295)) | ~m1_subset_1(B_295, k1_zfmisc_1(k2_zfmisc_1(A_294, A_294))) | ~v3_funct_2(B_295, A_294, A_294) | ~v1_funct_2(B_295, A_294, A_294) | ~v1_funct_1(B_295))), inference(resolution, [status(thm)], [c_30, c_2760])).
% 9.15/3.36  tff(c_3094, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_3082])).
% 9.15/3.36  tff(c_3111, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2564, c_2562, c_2562, c_2562, c_3094])).
% 9.15/3.36  tff(c_75, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.15/3.36  tff(c_81, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_75])).
% 9.15/3.36  tff(c_90, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_81])).
% 9.15/3.36  tff(c_283, plain, (![C_84, A_85, B_86]: (v2_funct_1(C_84) | ~v3_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.15/3.36  tff(c_289, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_283])).
% 9.15/3.36  tff(c_297, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_289])).
% 9.15/3.36  tff(c_345, plain, (![A_95, B_96, C_97, D_98]: (r2_relset_1(A_95, B_96, C_97, C_97) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.15/3.36  tff(c_355, plain, (![A_99, C_100]: (r2_relset_1(A_99, A_99, C_100, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))))), inference(resolution, [status(thm)], [c_40, c_345])).
% 9.15/3.36  tff(c_363, plain, (![A_25]: (r2_relset_1(A_25, A_25, k6_partfun1(A_25), k6_partfun1(A_25)))), inference(resolution, [status(thm)], [c_40, c_355])).
% 9.15/3.36  tff(c_144, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.15/3.36  tff(c_156, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_144])).
% 9.15/3.36  tff(c_317, plain, (![A_92, B_93]: (k1_relset_1(A_92, A_92, B_93)=A_92 | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.15/3.36  tff(c_323, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_317])).
% 9.15/3.36  tff(c_332, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_156, c_323])).
% 9.15/3.36  tff(c_10, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.15/3.36  tff(c_59, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 9.15/3.36  tff(c_403, plain, (![A_117, B_118]: (k2_funct_2(A_117, B_118)=k2_funct_1(B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.15/3.36  tff(c_409, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_403])).
% 9.15/3.36  tff(c_417, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_409])).
% 9.15/3.36  tff(c_385, plain, (![A_112, B_113]: (v1_funct_1(k2_funct_2(A_112, B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_zfmisc_1(A_112, A_112))) | ~v3_funct_2(B_113, A_112, A_112) | ~v1_funct_2(B_113, A_112, A_112) | ~v1_funct_1(B_113))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.15/3.36  tff(c_391, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_385])).
% 9.15/3.36  tff(c_399, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_391])).
% 9.15/3.36  tff(c_419, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_399])).
% 9.15/3.36  tff(c_569, plain, (![C_133, E_134, A_131, D_129, F_132, B_130]: (k1_partfun1(A_131, B_130, C_133, D_129, E_134, F_132)=k5_relat_1(E_134, F_132) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_133, D_129))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.15/3.36  tff(c_2079, plain, (![E_185, A_187, B_186, A_183, B_184]: (k1_partfun1(A_183, B_184, A_187, A_187, E_185, k2_funct_2(A_187, B_186))=k5_relat_1(E_185, k2_funct_2(A_187, B_186)) | ~v1_funct_1(k2_funct_2(A_187, B_186)) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(E_185) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_186, A_187, A_187) | ~v1_funct_2(B_186, A_187, A_187) | ~v1_funct_1(B_186))), inference(resolution, [status(thm)], [c_30, c_569])).
% 9.15/3.36  tff(c_2099, plain, (![A_187, B_186]: (k1_partfun1('#skF_1', '#skF_1', A_187, A_187, '#skF_2', k2_funct_2(A_187, B_186))=k5_relat_1('#skF_2', k2_funct_2(A_187, B_186)) | ~v1_funct_1(k2_funct_2(A_187, B_186)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_186, A_187, A_187) | ~v1_funct_2(B_186, A_187, A_187) | ~v1_funct_1(B_186))), inference(resolution, [status(thm)], [c_52, c_2079])).
% 9.15/3.36  tff(c_2144, plain, (![A_188, B_189]: (k1_partfun1('#skF_1', '#skF_1', A_188, A_188, '#skF_2', k2_funct_2(A_188, B_189))=k5_relat_1('#skF_2', k2_funct_2(A_188, B_189)) | ~v1_funct_1(k2_funct_2(A_188, B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_189, A_188, A_188) | ~v1_funct_2(B_189, A_188, A_188) | ~v1_funct_1(B_189))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2099])).
% 9.15/3.36  tff(c_2164, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2144])).
% 9.15/3.36  tff(c_2193, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_419, c_417, c_417, c_417, c_2164])).
% 9.15/3.36  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 9.15/3.36  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 9.15/3.36  tff(c_420, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_74])).
% 9.15/3.36  tff(c_2195, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2193, c_420])).
% 9.15/3.36  tff(c_2202, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_2195])).
% 9.15/3.36  tff(c_2205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_58, c_297, c_363, c_332, c_2202])).
% 9.15/3.36  tff(c_2206, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_50])).
% 9.15/3.36  tff(c_2566, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2206])).
% 9.15/3.36  tff(c_3176, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3111, c_2566])).
% 9.15/3.36  tff(c_3183, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3176])).
% 9.15/3.36  tff(c_3186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2223, c_58, c_2447, c_2484, c_2366, c_3183])).
% 9.15/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.36  
% 9.15/3.36  Inference rules
% 9.15/3.36  ----------------------
% 9.15/3.37  #Ref     : 0
% 9.15/3.37  #Sup     : 672
% 9.15/3.37  #Fact    : 0
% 9.15/3.37  #Define  : 0
% 9.15/3.37  #Split   : 3
% 9.15/3.37  #Chain   : 0
% 9.15/3.37  #Close   : 0
% 9.15/3.37  
% 9.15/3.37  Ordering : KBO
% 9.15/3.37  
% 9.15/3.37  Simplification rules
% 9.15/3.37  ----------------------
% 9.15/3.37  #Subsume      : 6
% 9.15/3.37  #Demod        : 1495
% 9.15/3.37  #Tautology    : 269
% 9.15/3.37  #SimpNegUnit  : 2
% 9.15/3.37  #BackRed      : 55
% 9.15/3.37  
% 9.15/3.37  #Partial instantiations: 0
% 9.15/3.37  #Strategies tried      : 1
% 9.15/3.37  
% 9.15/3.37  Timing (in seconds)
% 9.15/3.37  ----------------------
% 9.15/3.37  Preprocessing        : 0.57
% 9.15/3.37  Parsing              : 0.30
% 9.15/3.37  CNF conversion       : 0.04
% 9.15/3.37  Main loop            : 1.85
% 9.15/3.37  Inferencing          : 0.64
% 9.15/3.37  Reduction            : 0.71
% 9.15/3.37  Demodulation         : 0.55
% 9.15/3.37  BG Simplification    : 0.06
% 9.15/3.37  Subsumption          : 0.30
% 9.15/3.37  Abstraction          : 0.07
% 9.15/3.37  MUC search           : 0.00
% 9.15/3.37  Cooper               : 0.00
% 9.15/3.37  Total                : 2.50
% 9.15/3.37  Index Insertion      : 0.00
% 9.15/3.37  Index Deletion       : 0.00
% 9.15/3.37  Index Matching       : 0.00
% 9.15/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
