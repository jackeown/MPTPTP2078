%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:04 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 347 expanded)
%              Number of leaves         :   44 ( 151 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 (1065 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_106,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_91,axiom,(
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

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_83,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2420,plain,(
    ! [C_234,A_235,B_236] :
      ( v2_funct_1(C_234)
      | ~ v3_funct_2(C_234,A_235,B_236)
      | ~ v1_funct_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2429,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2420])).

tff(c_2434,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2429])).

tff(c_36,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_23,B_24] : m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2454,plain,(
    ! [A_246,B_247,C_248,D_249] :
      ( r2_relset_1(A_246,B_247,C_248,C_248)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247)))
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2464,plain,(
    ! [A_250,B_251,C_252] :
      ( r2_relset_1(A_250,B_251,C_252,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2454])).

tff(c_2472,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_36,c_2464])).

tff(c_113,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_2244,plain,(
    ! [B_201,A_202] :
      ( k2_relat_1(B_201) = A_202
      | ~ v2_funct_2(B_201,A_202)
      | ~ v5_relat_1(B_201,A_202)
      | ~ v1_relat_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2250,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_2244])).

tff(c_2259,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2250])).

tff(c_2263,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2259])).

tff(c_2336,plain,(
    ! [C_220,B_221,A_222] :
      ( v2_funct_2(C_220,B_221)
      | ~ v3_funct_2(C_220,A_222,B_221)
      | ~ v1_funct_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2345,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2336])).

tff(c_2350,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2345])).

tff(c_2352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2263,c_2350])).

tff(c_2353,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2259])).

tff(c_52,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2522,plain,(
    ! [A_263,B_264] :
      ( k2_funct_2(A_263,B_264) = k2_funct_1(B_264)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(k2_zfmisc_1(A_263,A_263)))
      | ~ v3_funct_2(B_264,A_263,A_263)
      | ~ v1_funct_2(B_264,A_263,A_263)
      | ~ v1_funct_1(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2532,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2522])).

tff(c_2537,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2532])).

tff(c_2505,plain,(
    ! [A_260,B_261] :
      ( v1_funct_1(k2_funct_2(A_260,B_261))
      | ~ m1_subset_1(B_261,k1_zfmisc_1(k2_zfmisc_1(A_260,A_260)))
      | ~ v3_funct_2(B_261,A_260,A_260)
      | ~ v1_funct_2(B_261,A_260,A_260)
      | ~ v1_funct_1(B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2515,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2505])).

tff(c_2520,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2515])).

tff(c_2538,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2520])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2683,plain,(
    ! [F_276,B_274,D_273,C_277,E_278,A_275] :
      ( k1_partfun1(A_275,B_274,C_277,D_273,E_278,F_276) = k5_relat_1(E_278,F_276)
      | ~ m1_subset_1(F_276,k1_zfmisc_1(k2_zfmisc_1(C_277,D_273)))
      | ~ v1_funct_1(F_276)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_275,B_274)))
      | ~ v1_funct_1(E_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2693,plain,(
    ! [A_275,B_274,E_278] :
      ( k1_partfun1(A_275,B_274,'#skF_2','#skF_2',E_278,'#skF_3') = k5_relat_1(E_278,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_275,B_274)))
      | ~ v1_funct_1(E_278) ) ),
    inference(resolution,[status(thm)],[c_58,c_2683])).

tff(c_2718,plain,(
    ! [A_279,B_280,E_281] :
      ( k1_partfun1(A_279,B_280,'#skF_2','#skF_2',E_281,'#skF_3') = k5_relat_1(E_281,'#skF_3')
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280)))
      | ~ v1_funct_1(E_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2693])).

tff(c_3067,plain,(
    ! [A_292,B_293] :
      ( k1_partfun1(A_292,A_292,'#skF_2','#skF_2',k2_funct_2(A_292,B_293),'#skF_3') = k5_relat_1(k2_funct_2(A_292,B_293),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_292,B_293))
      | ~ m1_subset_1(B_293,k1_zfmisc_1(k2_zfmisc_1(A_292,A_292)))
      | ~ v3_funct_2(B_293,A_292,A_292)
      | ~ v1_funct_2(B_293,A_292,A_292)
      | ~ v1_funct_1(B_293) ) ),
    inference(resolution,[status(thm)],[c_26,c_2718])).

tff(c_3082,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3067])).

tff(c_3097,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2538,c_2537,c_2537,c_2537,c_3082])).

tff(c_306,plain,(
    ! [C_96,A_97,B_98] :
      ( v2_funct_1(C_96)
      | ~ v3_funct_2(C_96,A_97,B_98)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_315,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_306])).

tff(c_320,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_315])).

tff(c_369,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( r2_relset_1(A_112,B_113,C_114,C_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_395,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_relset_1(A_118,B_119,C_120,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(resolution,[status(thm)],[c_46,c_369])).

tff(c_403,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_36,c_395])).

tff(c_253,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_265,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_253])).

tff(c_340,plain,(
    ! [A_108,B_109] :
      ( k1_relset_1(A_108,A_108,B_109) = A_108
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_350,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_340])).

tff(c_357,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_265,c_350])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4])).

tff(c_408,plain,(
    ! [A_125,B_126] :
      ( k2_funct_2(A_125,B_126) = k2_funct_1(B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(A_125,A_125)))
      | ~ v3_funct_2(B_126,A_125,A_125)
      | ~ v1_funct_2(B_126,A_125,A_125)
      | ~ v1_funct_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_418,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_408])).

tff(c_423,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_418])).

tff(c_379,plain,(
    ! [A_116,B_117] :
      ( v1_funct_1(k2_funct_2(A_116,B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_zfmisc_1(A_116,A_116)))
      | ~ v3_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_389,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_379])).

tff(c_394,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_389])).

tff(c_437,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_394])).

tff(c_580,plain,(
    ! [B_137,C_140,A_138,F_139,D_136,E_141] :
      ( k1_partfun1(A_138,B_137,C_140,D_136,E_141,F_139) = k5_relat_1(E_141,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_136)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2122,plain,(
    ! [A_194,B_196,A_192,E_195,B_193] :
      ( k1_partfun1(A_192,B_196,A_194,A_194,E_195,k2_funct_2(A_194,B_193)) = k5_relat_1(E_195,k2_funct_2(A_194,B_193))
      | ~ v1_funct_1(k2_funct_2(A_194,B_193))
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_192,B_196)))
      | ~ v1_funct_1(E_195)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_193,A_194,A_194)
      | ~ v1_funct_2(B_193,A_194,A_194)
      | ~ v1_funct_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_26,c_580])).

tff(c_2144,plain,(
    ! [A_194,B_193] :
      ( k1_partfun1('#skF_2','#skF_2',A_194,A_194,'#skF_3',k2_funct_2(A_194,B_193)) = k5_relat_1('#skF_3',k2_funct_2(A_194,B_193))
      | ~ v1_funct_1(k2_funct_2(A_194,B_193))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_193,A_194,A_194)
      | ~ v1_funct_2(B_193,A_194,A_194)
      | ~ v1_funct_1(B_193) ) ),
    inference(resolution,[status(thm)],[c_58,c_2122])).

tff(c_2178,plain,(
    ! [A_197,B_198] :
      ( k1_partfun1('#skF_2','#skF_2',A_197,A_197,'#skF_3',k2_funct_2(A_197,B_198)) = k5_relat_1('#skF_3',k2_funct_2(A_197,B_198))
      | ~ v1_funct_1(k2_funct_2(A_197,B_198))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_zfmisc_1(A_197,A_197)))
      | ~ v3_funct_2(B_198,A_197,A_197)
      | ~ v1_funct_2(B_198,A_197,A_197)
      | ~ v1_funct_1(B_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2144])).

tff(c_2201,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2178])).

tff(c_2228,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_437,c_423,c_423,c_423,c_2201])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_127,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_438,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_127])).

tff(c_2229,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2228,c_438])).

tff(c_2236,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2229])).

tff(c_2239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_320,c_403,c_357,c_2236])).

tff(c_2240,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2539,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2537,c_2240])).

tff(c_3109,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_2539])).

tff(c_3116,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_3109])).

tff(c_3119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_2434,c_2472,c_2353,c_3116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:42:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.14  
% 5.97/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.14  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.97/2.14  
% 5.97/2.14  %Foreground sorts:
% 5.97/2.14  
% 5.97/2.14  
% 5.97/2.14  %Background operators:
% 5.97/2.14  
% 5.97/2.14  
% 5.97/2.14  %Foreground operators:
% 5.97/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.97/2.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.97/2.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.97/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.97/2.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.97/2.14  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.97/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.97/2.14  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.97/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.97/2.14  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.97/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.97/2.14  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.97/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.97/2.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.97/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.97/2.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.97/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.97/2.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.97/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.97/2.14  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.97/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.97/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.97/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.97/2.14  
% 5.97/2.16  tff(f_149, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.97/2.16  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.97/2.16  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.97/2.16  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.97/2.16  tff(f_106, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 5.97/2.16  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.97/2.16  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.97/2.16  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.97/2.16  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.97/2.16  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.97/2.16  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.97/2.16  tff(f_91, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.97/2.16  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.97/2.16  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.97/2.16  tff(f_136, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.97/2.16  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.97/2.16  tff(c_83, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.97/2.16  tff(c_96, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_83])).
% 5.97/2.16  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.97/2.16  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.97/2.16  tff(c_2420, plain, (![C_234, A_235, B_236]: (v2_funct_1(C_234) | ~v3_funct_2(C_234, A_235, B_236) | ~v1_funct_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.97/2.16  tff(c_2429, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2420])).
% 5.97/2.16  tff(c_2434, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2429])).
% 5.97/2.16  tff(c_36, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.97/2.16  tff(c_46, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.97/2.16  tff(c_2454, plain, (![A_246, B_247, C_248, D_249]: (r2_relset_1(A_246, B_247, C_248, C_248) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.97/2.16  tff(c_2464, plain, (![A_250, B_251, C_252]: (r2_relset_1(A_250, B_251, C_252, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(resolution, [status(thm)], [c_46, c_2454])).
% 5.97/2.16  tff(c_2472, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_36, c_2464])).
% 5.97/2.16  tff(c_113, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.97/2.16  tff(c_126, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_113])).
% 5.97/2.16  tff(c_2244, plain, (![B_201, A_202]: (k2_relat_1(B_201)=A_202 | ~v2_funct_2(B_201, A_202) | ~v5_relat_1(B_201, A_202) | ~v1_relat_1(B_201))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.97/2.16  tff(c_2250, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_2244])).
% 5.97/2.16  tff(c_2259, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2250])).
% 5.97/2.16  tff(c_2263, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2259])).
% 5.97/2.16  tff(c_2336, plain, (![C_220, B_221, A_222]: (v2_funct_2(C_220, B_221) | ~v3_funct_2(C_220, A_222, B_221) | ~v1_funct_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.97/2.16  tff(c_2345, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2336])).
% 5.97/2.16  tff(c_2350, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2345])).
% 5.97/2.16  tff(c_2352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2263, c_2350])).
% 5.97/2.16  tff(c_2353, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2259])).
% 5.97/2.16  tff(c_52, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.97/2.16  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.97/2.16  tff(c_66, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2])).
% 5.97/2.16  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.97/2.16  tff(c_2522, plain, (![A_263, B_264]: (k2_funct_2(A_263, B_264)=k2_funct_1(B_264) | ~m1_subset_1(B_264, k1_zfmisc_1(k2_zfmisc_1(A_263, A_263))) | ~v3_funct_2(B_264, A_263, A_263) | ~v1_funct_2(B_264, A_263, A_263) | ~v1_funct_1(B_264))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.97/2.16  tff(c_2532, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2522])).
% 5.97/2.16  tff(c_2537, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2532])).
% 5.97/2.16  tff(c_2505, plain, (![A_260, B_261]: (v1_funct_1(k2_funct_2(A_260, B_261)) | ~m1_subset_1(B_261, k1_zfmisc_1(k2_zfmisc_1(A_260, A_260))) | ~v3_funct_2(B_261, A_260, A_260) | ~v1_funct_2(B_261, A_260, A_260) | ~v1_funct_1(B_261))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.97/2.16  tff(c_2515, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2505])).
% 5.97/2.16  tff(c_2520, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2515])).
% 5.97/2.16  tff(c_2538, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2520])).
% 5.97/2.16  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.97/2.16  tff(c_2683, plain, (![F_276, B_274, D_273, C_277, E_278, A_275]: (k1_partfun1(A_275, B_274, C_277, D_273, E_278, F_276)=k5_relat_1(E_278, F_276) | ~m1_subset_1(F_276, k1_zfmisc_1(k2_zfmisc_1(C_277, D_273))) | ~v1_funct_1(F_276) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_275, B_274))) | ~v1_funct_1(E_278))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.97/2.16  tff(c_2693, plain, (![A_275, B_274, E_278]: (k1_partfun1(A_275, B_274, '#skF_2', '#skF_2', E_278, '#skF_3')=k5_relat_1(E_278, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_275, B_274))) | ~v1_funct_1(E_278))), inference(resolution, [status(thm)], [c_58, c_2683])).
% 5.97/2.16  tff(c_2718, plain, (![A_279, B_280, E_281]: (k1_partfun1(A_279, B_280, '#skF_2', '#skF_2', E_281, '#skF_3')=k5_relat_1(E_281, '#skF_3') | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))) | ~v1_funct_1(E_281))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2693])).
% 5.97/2.16  tff(c_3067, plain, (![A_292, B_293]: (k1_partfun1(A_292, A_292, '#skF_2', '#skF_2', k2_funct_2(A_292, B_293), '#skF_3')=k5_relat_1(k2_funct_2(A_292, B_293), '#skF_3') | ~v1_funct_1(k2_funct_2(A_292, B_293)) | ~m1_subset_1(B_293, k1_zfmisc_1(k2_zfmisc_1(A_292, A_292))) | ~v3_funct_2(B_293, A_292, A_292) | ~v1_funct_2(B_293, A_292, A_292) | ~v1_funct_1(B_293))), inference(resolution, [status(thm)], [c_26, c_2718])).
% 5.97/2.16  tff(c_3082, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3067])).
% 5.97/2.16  tff(c_3097, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2538, c_2537, c_2537, c_2537, c_3082])).
% 5.97/2.16  tff(c_306, plain, (![C_96, A_97, B_98]: (v2_funct_1(C_96) | ~v3_funct_2(C_96, A_97, B_98) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.97/2.16  tff(c_315, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_306])).
% 5.97/2.16  tff(c_320, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_315])).
% 5.97/2.16  tff(c_369, plain, (![A_112, B_113, C_114, D_115]: (r2_relset_1(A_112, B_113, C_114, C_114) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.97/2.16  tff(c_395, plain, (![A_118, B_119, C_120]: (r2_relset_1(A_118, B_119, C_120, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(resolution, [status(thm)], [c_46, c_369])).
% 5.97/2.16  tff(c_403, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_36, c_395])).
% 5.97/2.16  tff(c_253, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.97/2.16  tff(c_265, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_253])).
% 5.97/2.16  tff(c_340, plain, (![A_108, B_109]: (k1_relset_1(A_108, A_108, B_109)=A_108 | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.97/2.16  tff(c_350, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_340])).
% 5.97/2.16  tff(c_357, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_265, c_350])).
% 5.97/2.16  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.97/2.16  tff(c_65, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4])).
% 5.97/2.16  tff(c_408, plain, (![A_125, B_126]: (k2_funct_2(A_125, B_126)=k2_funct_1(B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(k2_zfmisc_1(A_125, A_125))) | ~v3_funct_2(B_126, A_125, A_125) | ~v1_funct_2(B_126, A_125, A_125) | ~v1_funct_1(B_126))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.97/2.16  tff(c_418, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_408])).
% 5.97/2.16  tff(c_423, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_418])).
% 5.97/2.16  tff(c_379, plain, (![A_116, B_117]: (v1_funct_1(k2_funct_2(A_116, B_117)) | ~m1_subset_1(B_117, k1_zfmisc_1(k2_zfmisc_1(A_116, A_116))) | ~v3_funct_2(B_117, A_116, A_116) | ~v1_funct_2(B_117, A_116, A_116) | ~v1_funct_1(B_117))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.97/2.16  tff(c_389, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_379])).
% 5.97/2.16  tff(c_394, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_389])).
% 5.97/2.16  tff(c_437, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_394])).
% 5.97/2.16  tff(c_580, plain, (![B_137, C_140, A_138, F_139, D_136, E_141]: (k1_partfun1(A_138, B_137, C_140, D_136, E_141, F_139)=k5_relat_1(E_141, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_136))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.97/2.16  tff(c_2122, plain, (![A_194, B_196, A_192, E_195, B_193]: (k1_partfun1(A_192, B_196, A_194, A_194, E_195, k2_funct_2(A_194, B_193))=k5_relat_1(E_195, k2_funct_2(A_194, B_193)) | ~v1_funct_1(k2_funct_2(A_194, B_193)) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_192, B_196))) | ~v1_funct_1(E_195) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_193, A_194, A_194) | ~v1_funct_2(B_193, A_194, A_194) | ~v1_funct_1(B_193))), inference(resolution, [status(thm)], [c_26, c_580])).
% 5.97/2.16  tff(c_2144, plain, (![A_194, B_193]: (k1_partfun1('#skF_2', '#skF_2', A_194, A_194, '#skF_3', k2_funct_2(A_194, B_193))=k5_relat_1('#skF_3', k2_funct_2(A_194, B_193)) | ~v1_funct_1(k2_funct_2(A_194, B_193)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_193, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_193, A_194, A_194) | ~v1_funct_2(B_193, A_194, A_194) | ~v1_funct_1(B_193))), inference(resolution, [status(thm)], [c_58, c_2122])).
% 5.97/2.16  tff(c_2178, plain, (![A_197, B_198]: (k1_partfun1('#skF_2', '#skF_2', A_197, A_197, '#skF_3', k2_funct_2(A_197, B_198))=k5_relat_1('#skF_3', k2_funct_2(A_197, B_198)) | ~v1_funct_1(k2_funct_2(A_197, B_198)) | ~m1_subset_1(B_198, k1_zfmisc_1(k2_zfmisc_1(A_197, A_197))) | ~v3_funct_2(B_198, A_197, A_197) | ~v1_funct_2(B_198, A_197, A_197) | ~v1_funct_1(B_198))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2144])).
% 5.97/2.16  tff(c_2201, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2178])).
% 5.97/2.16  tff(c_2228, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_437, c_423, c_423, c_423, c_2201])).
% 5.97/2.16  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.97/2.16  tff(c_127, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 5.97/2.16  tff(c_438, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_127])).
% 5.97/2.16  tff(c_2229, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2228, c_438])).
% 5.97/2.16  tff(c_2236, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_65, c_2229])).
% 5.97/2.16  tff(c_2239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_320, c_403, c_357, c_2236])).
% 5.97/2.16  tff(c_2240, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 5.97/2.16  tff(c_2539, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2537, c_2240])).
% 5.97/2.16  tff(c_3109, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_2539])).
% 5.97/2.16  tff(c_3116, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_3109])).
% 5.97/2.16  tff(c_3119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_2434, c_2472, c_2353, c_3116])).
% 5.97/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.16  
% 5.97/2.16  Inference rules
% 5.97/2.16  ----------------------
% 5.97/2.16  #Ref     : 0
% 5.97/2.16  #Sup     : 663
% 5.97/2.16  #Fact    : 0
% 5.97/2.16  #Define  : 0
% 5.97/2.16  #Split   : 3
% 5.97/2.16  #Chain   : 0
% 5.97/2.16  #Close   : 0
% 5.97/2.16  
% 5.97/2.16  Ordering : KBO
% 5.97/2.16  
% 5.97/2.16  Simplification rules
% 5.97/2.16  ----------------------
% 5.97/2.16  #Subsume      : 6
% 5.97/2.16  #Demod        : 1525
% 5.97/2.16  #Tautology    : 264
% 5.97/2.16  #SimpNegUnit  : 2
% 5.97/2.16  #BackRed      : 61
% 5.97/2.16  
% 5.97/2.16  #Partial instantiations: 0
% 5.97/2.16  #Strategies tried      : 1
% 5.97/2.16  
% 5.97/2.16  Timing (in seconds)
% 5.97/2.16  ----------------------
% 5.97/2.16  Preprocessing        : 0.35
% 5.97/2.16  Parsing              : 0.19
% 5.97/2.16  CNF conversion       : 0.02
% 5.97/2.16  Main loop            : 1.02
% 5.97/2.16  Inferencing          : 0.34
% 5.97/2.16  Reduction            : 0.39
% 5.97/2.16  Demodulation         : 0.30
% 5.97/2.17  BG Simplification    : 0.03
% 5.97/2.17  Subsumption          : 0.19
% 5.97/2.17  Abstraction          : 0.04
% 5.97/2.17  MUC search           : 0.00
% 5.97/2.17  Cooper               : 0.00
% 5.97/2.17  Total                : 1.42
% 5.97/2.17  Index Insertion      : 0.00
% 5.97/2.17  Index Deletion       : 0.00
% 5.97/2.17  Index Matching       : 0.00
% 5.97/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
