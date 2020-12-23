%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:04 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 346 expanded)
%              Number of leaves         :   43 ( 150 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 (1065 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_106,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

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

tff(c_2208,plain,(
    ! [C_230,A_231,B_232] :
      ( v2_funct_1(C_230)
      | ~ v3_funct_2(C_230,A_231,B_232)
      | ~ v1_funct_1(C_230)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2217,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2208])).

tff(c_2224,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2217])).

tff(c_36,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_23,B_24] : m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2265,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( r2_relset_1(A_244,B_245,C_246,C_246)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2284,plain,(
    ! [A_248,B_249,C_250] :
      ( r2_relset_1(A_248,B_249,C_250,C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2265])).

tff(c_2292,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_36,c_2284])).

tff(c_113,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_2028,plain,(
    ! [B_197,A_198] :
      ( k2_relat_1(B_197) = A_198
      | ~ v2_funct_2(B_197,A_198)
      | ~ v5_relat_1(B_197,A_198)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2034,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_2028])).

tff(c_2043,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2034])).

tff(c_2047,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2043])).

tff(c_2122,plain,(
    ! [C_216,B_217,A_218] :
      ( v2_funct_2(C_216,B_217)
      | ~ v3_funct_2(C_216,A_218,B_217)
      | ~ v1_funct_1(C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2131,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2122])).

tff(c_2138,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2131])).

tff(c_2140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2047,c_2138])).

tff(c_2141,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2043])).

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

tff(c_2317,plain,(
    ! [A_259,B_260] :
      ( k2_funct_2(A_259,B_260) = k2_funct_1(B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2327,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2317])).

tff(c_2334,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2327])).

tff(c_2297,plain,(
    ! [A_255,B_256] :
      ( v1_funct_1(k2_funct_2(A_255,B_256))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k2_zfmisc_1(A_255,A_255)))
      | ~ v3_funct_2(B_256,A_255,A_255)
      | ~ v1_funct_2(B_256,A_255,A_255)
      | ~ v1_funct_1(B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2307,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2297])).

tff(c_2314,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2307])).

tff(c_2335,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2314])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2499,plain,(
    ! [F_277,D_274,C_278,B_275,A_276,E_279] :
      ( k1_partfun1(A_276,B_275,C_278,D_274,E_279,F_277) = k5_relat_1(E_279,F_277)
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(C_278,D_274)))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_276,B_275)))
      | ~ v1_funct_1(E_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2509,plain,(
    ! [A_276,B_275,E_279] :
      ( k1_partfun1(A_276,B_275,'#skF_2','#skF_2',E_279,'#skF_3') = k5_relat_1(E_279,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_276,B_275)))
      | ~ v1_funct_1(E_279) ) ),
    inference(resolution,[status(thm)],[c_58,c_2499])).

tff(c_2532,plain,(
    ! [A_280,B_281,E_282] :
      ( k1_partfun1(A_280,B_281,'#skF_2','#skF_2',E_282,'#skF_3') = k5_relat_1(E_282,'#skF_3')
      | ~ m1_subset_1(E_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281)))
      | ~ v1_funct_1(E_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2509])).

tff(c_2792,plain,(
    ! [A_290,B_291] :
      ( k1_partfun1(A_290,A_290,'#skF_2','#skF_2',k2_funct_2(A_290,B_291),'#skF_3') = k5_relat_1(k2_funct_2(A_290,B_291),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_290,B_291))
      | ~ m1_subset_1(B_291,k1_zfmisc_1(k2_zfmisc_1(A_290,A_290)))
      | ~ v3_funct_2(B_291,A_290,A_290)
      | ~ v1_funct_2(B_291,A_290,A_290)
      | ~ v1_funct_1(B_291) ) ),
    inference(resolution,[status(thm)],[c_26,c_2532])).

tff(c_2805,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2792])).

tff(c_2819,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2335,c_2334,c_2334,c_2334,c_2805])).

tff(c_310,plain,(
    ! [C_96,A_97,B_98] :
      ( v2_funct_1(C_96)
      | ~ v3_funct_2(C_96,A_97,B_98)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_319,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_310])).

tff(c_326,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_319])).

tff(c_378,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( r2_relset_1(A_112,B_113,C_114,C_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_406,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_relset_1(A_118,B_119,C_120,C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(resolution,[status(thm)],[c_46,c_378])).

tff(c_414,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_36,c_406])).

tff(c_257,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_269,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_257])).

tff(c_348,plain,(
    ! [A_108,B_109] :
      ( k1_relset_1(A_108,A_108,B_109) = A_108
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_358,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_348])).

tff(c_366,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_269,c_358])).

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

tff(c_420,plain,(
    ! [A_126,B_127] :
      ( k2_funct_2(A_126,B_127) = k2_funct_1(B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1(A_126,A_126)))
      | ~ v3_funct_2(B_127,A_126,A_126)
      | ~ v1_funct_2(B_127,A_126,A_126)
      | ~ v1_funct_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_430,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_420])).

tff(c_437,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_430])).

tff(c_388,plain,(
    ! [A_116,B_117] :
      ( v1_funct_1(k2_funct_2(A_116,B_117))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_zfmisc_1(A_116,A_116)))
      | ~ v3_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_398,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_388])).

tff(c_405,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_398])).

tff(c_438,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_405])).

tff(c_596,plain,(
    ! [C_144,E_145,A_142,F_143,B_141,D_140] :
      ( k1_partfun1(A_142,B_141,C_144,D_140,E_145,F_143) = k5_relat_1(E_145,F_143)
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_144,D_140)))
      | ~ v1_funct_1(F_143)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1893,plain,(
    ! [B_188,E_191,B_192,A_190,A_189] :
      ( k1_partfun1(A_190,B_192,A_189,A_189,E_191,k2_funct_2(A_189,B_188)) = k5_relat_1(E_191,k2_funct_2(A_189,B_188))
      | ~ v1_funct_1(k2_funct_2(A_189,B_188))
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_190,B_192)))
      | ~ v1_funct_1(E_191)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_188,A_189,A_189)
      | ~ v1_funct_2(B_188,A_189,A_189)
      | ~ v1_funct_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_26,c_596])).

tff(c_1913,plain,(
    ! [A_189,B_188] :
      ( k1_partfun1('#skF_2','#skF_2',A_189,A_189,'#skF_3',k2_funct_2(A_189,B_188)) = k5_relat_1('#skF_3',k2_funct_2(A_189,B_188))
      | ~ v1_funct_1(k2_funct_2(A_189,B_188))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_188,A_189,A_189)
      | ~ v1_funct_2(B_188,A_189,A_189)
      | ~ v1_funct_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_58,c_1893])).

tff(c_1965,plain,(
    ! [A_193,B_194] :
      ( k1_partfun1('#skF_2','#skF_2',A_193,A_193,'#skF_3',k2_funct_2(A_193,B_194)) = k5_relat_1('#skF_3',k2_funct_2(A_193,B_194))
      | ~ v1_funct_1(k2_funct_2(A_193,B_194))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_193,A_193)))
      | ~ v3_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_2(B_194,A_193,A_193)
      | ~ v1_funct_1(B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1913])).

tff(c_1986,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1965])).

tff(c_2012,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_438,c_437,c_437,c_437,c_1986])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_127,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_439,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_127])).

tff(c_2013,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_439])).

tff(c_2020,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2013])).

tff(c_2023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_326,c_414,c_366,c_2020])).

tff(c_2024,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2336,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2024])).

tff(c_2958,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_2336])).

tff(c_2965,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2958])).

tff(c_2968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_64,c_2224,c_2292,c_2141,c_2965])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.61/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.08  
% 5.71/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.08  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.71/2.08  
% 5.71/2.08  %Foreground sorts:
% 5.71/2.08  
% 5.71/2.08  
% 5.71/2.08  %Background operators:
% 5.71/2.08  
% 5.71/2.08  
% 5.71/2.08  %Foreground operators:
% 5.71/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.71/2.08  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.71/2.08  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.71/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.71/2.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.71/2.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.71/2.08  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.71/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.71/2.08  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.71/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.71/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.71/2.08  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.71/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.71/2.08  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.71/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.71/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.71/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.71/2.08  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.71/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.71/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.71/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.71/2.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.71/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.71/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.71/2.08  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.71/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.71/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.71/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.71/2.08  
% 5.71/2.10  tff(f_149, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.71/2.10  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.71/2.10  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.71/2.10  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.71/2.10  tff(f_106, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_partfun1)).
% 5.71/2.10  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.71/2.10  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.71/2.10  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.71/2.10  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.71/2.10  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.71/2.10  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.71/2.10  tff(f_91, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.71/2.10  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.71/2.10  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.71/2.10  tff(f_136, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.71/2.10  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.71/2.10  tff(c_83, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.71/2.10  tff(c_96, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_83])).
% 5.71/2.10  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.71/2.10  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.71/2.10  tff(c_2208, plain, (![C_230, A_231, B_232]: (v2_funct_1(C_230) | ~v3_funct_2(C_230, A_231, B_232) | ~v1_funct_1(C_230) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.71/2.10  tff(c_2217, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2208])).
% 5.71/2.10  tff(c_2224, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2217])).
% 5.71/2.10  tff(c_36, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.71/2.10  tff(c_46, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.71/2.10  tff(c_2265, plain, (![A_244, B_245, C_246, D_247]: (r2_relset_1(A_244, B_245, C_246, C_246) | ~m1_subset_1(D_247, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.71/2.10  tff(c_2284, plain, (![A_248, B_249, C_250]: (r2_relset_1(A_248, B_249, C_250, C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(resolution, [status(thm)], [c_46, c_2265])).
% 5.71/2.10  tff(c_2292, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_36, c_2284])).
% 5.71/2.10  tff(c_113, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.71/2.10  tff(c_126, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_113])).
% 5.71/2.10  tff(c_2028, plain, (![B_197, A_198]: (k2_relat_1(B_197)=A_198 | ~v2_funct_2(B_197, A_198) | ~v5_relat_1(B_197, A_198) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.71/2.10  tff(c_2034, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_2028])).
% 5.71/2.10  tff(c_2043, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2034])).
% 5.71/2.10  tff(c_2047, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2043])).
% 5.71/2.10  tff(c_2122, plain, (![C_216, B_217, A_218]: (v2_funct_2(C_216, B_217) | ~v3_funct_2(C_216, A_218, B_217) | ~v1_funct_1(C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.71/2.10  tff(c_2131, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2122])).
% 5.71/2.10  tff(c_2138, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2131])).
% 5.71/2.10  tff(c_2140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2047, c_2138])).
% 5.71/2.10  tff(c_2141, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2043])).
% 5.71/2.10  tff(c_52, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.71/2.10  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.71/2.10  tff(c_66, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2])).
% 5.71/2.10  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.71/2.10  tff(c_2317, plain, (![A_259, B_260]: (k2_funct_2(A_259, B_260)=k2_funct_1(B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.71/2.10  tff(c_2327, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2317])).
% 5.71/2.10  tff(c_2334, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2327])).
% 5.71/2.10  tff(c_2297, plain, (![A_255, B_256]: (v1_funct_1(k2_funct_2(A_255, B_256)) | ~m1_subset_1(B_256, k1_zfmisc_1(k2_zfmisc_1(A_255, A_255))) | ~v3_funct_2(B_256, A_255, A_255) | ~v1_funct_2(B_256, A_255, A_255) | ~v1_funct_1(B_256))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.10  tff(c_2307, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2297])).
% 5.71/2.10  tff(c_2314, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2307])).
% 5.71/2.10  tff(c_2335, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2314])).
% 5.71/2.10  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.10  tff(c_2499, plain, (![F_277, D_274, C_278, B_275, A_276, E_279]: (k1_partfun1(A_276, B_275, C_278, D_274, E_279, F_277)=k5_relat_1(E_279, F_277) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(C_278, D_274))) | ~v1_funct_1(F_277) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_276, B_275))) | ~v1_funct_1(E_279))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.71/2.10  tff(c_2509, plain, (![A_276, B_275, E_279]: (k1_partfun1(A_276, B_275, '#skF_2', '#skF_2', E_279, '#skF_3')=k5_relat_1(E_279, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_276, B_275))) | ~v1_funct_1(E_279))), inference(resolution, [status(thm)], [c_58, c_2499])).
% 5.71/2.10  tff(c_2532, plain, (![A_280, B_281, E_282]: (k1_partfun1(A_280, B_281, '#skF_2', '#skF_2', E_282, '#skF_3')=k5_relat_1(E_282, '#skF_3') | ~m1_subset_1(E_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))) | ~v1_funct_1(E_282))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2509])).
% 5.71/2.10  tff(c_2792, plain, (![A_290, B_291]: (k1_partfun1(A_290, A_290, '#skF_2', '#skF_2', k2_funct_2(A_290, B_291), '#skF_3')=k5_relat_1(k2_funct_2(A_290, B_291), '#skF_3') | ~v1_funct_1(k2_funct_2(A_290, B_291)) | ~m1_subset_1(B_291, k1_zfmisc_1(k2_zfmisc_1(A_290, A_290))) | ~v3_funct_2(B_291, A_290, A_290) | ~v1_funct_2(B_291, A_290, A_290) | ~v1_funct_1(B_291))), inference(resolution, [status(thm)], [c_26, c_2532])).
% 5.71/2.10  tff(c_2805, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2792])).
% 5.71/2.10  tff(c_2819, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2335, c_2334, c_2334, c_2334, c_2805])).
% 5.71/2.10  tff(c_310, plain, (![C_96, A_97, B_98]: (v2_funct_1(C_96) | ~v3_funct_2(C_96, A_97, B_98) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.71/2.10  tff(c_319, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_310])).
% 5.71/2.10  tff(c_326, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_319])).
% 5.71/2.10  tff(c_378, plain, (![A_112, B_113, C_114, D_115]: (r2_relset_1(A_112, B_113, C_114, C_114) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.71/2.10  tff(c_406, plain, (![A_118, B_119, C_120]: (r2_relset_1(A_118, B_119, C_120, C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(resolution, [status(thm)], [c_46, c_378])).
% 5.71/2.10  tff(c_414, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_36, c_406])).
% 5.71/2.10  tff(c_257, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.71/2.10  tff(c_269, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_257])).
% 5.71/2.10  tff(c_348, plain, (![A_108, B_109]: (k1_relset_1(A_108, A_108, B_109)=A_108 | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.71/2.10  tff(c_358, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_348])).
% 5.71/2.10  tff(c_366, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_269, c_358])).
% 5.71/2.10  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.71/2.10  tff(c_65, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4])).
% 5.71/2.10  tff(c_420, plain, (![A_126, B_127]: (k2_funct_2(A_126, B_127)=k2_funct_1(B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(k2_zfmisc_1(A_126, A_126))) | ~v3_funct_2(B_127, A_126, A_126) | ~v1_funct_2(B_127, A_126, A_126) | ~v1_funct_1(B_127))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.71/2.10  tff(c_430, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_420])).
% 5.71/2.10  tff(c_437, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_430])).
% 5.71/2.10  tff(c_388, plain, (![A_116, B_117]: (v1_funct_1(k2_funct_2(A_116, B_117)) | ~m1_subset_1(B_117, k1_zfmisc_1(k2_zfmisc_1(A_116, A_116))) | ~v3_funct_2(B_117, A_116, A_116) | ~v1_funct_2(B_117, A_116, A_116) | ~v1_funct_1(B_117))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.71/2.10  tff(c_398, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_388])).
% 5.71/2.10  tff(c_405, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_398])).
% 5.71/2.10  tff(c_438, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_405])).
% 5.71/2.10  tff(c_596, plain, (![C_144, E_145, A_142, F_143, B_141, D_140]: (k1_partfun1(A_142, B_141, C_144, D_140, E_145, F_143)=k5_relat_1(E_145, F_143) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_144, D_140))) | ~v1_funct_1(F_143) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.71/2.10  tff(c_1893, plain, (![B_188, E_191, B_192, A_190, A_189]: (k1_partfun1(A_190, B_192, A_189, A_189, E_191, k2_funct_2(A_189, B_188))=k5_relat_1(E_191, k2_funct_2(A_189, B_188)) | ~v1_funct_1(k2_funct_2(A_189, B_188)) | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_190, B_192))) | ~v1_funct_1(E_191) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_188, A_189, A_189) | ~v1_funct_2(B_188, A_189, A_189) | ~v1_funct_1(B_188))), inference(resolution, [status(thm)], [c_26, c_596])).
% 5.71/2.10  tff(c_1913, plain, (![A_189, B_188]: (k1_partfun1('#skF_2', '#skF_2', A_189, A_189, '#skF_3', k2_funct_2(A_189, B_188))=k5_relat_1('#skF_3', k2_funct_2(A_189, B_188)) | ~v1_funct_1(k2_funct_2(A_189, B_188)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_188, A_189, A_189) | ~v1_funct_2(B_188, A_189, A_189) | ~v1_funct_1(B_188))), inference(resolution, [status(thm)], [c_58, c_1893])).
% 5.71/2.10  tff(c_1965, plain, (![A_193, B_194]: (k1_partfun1('#skF_2', '#skF_2', A_193, A_193, '#skF_3', k2_funct_2(A_193, B_194))=k5_relat_1('#skF_3', k2_funct_2(A_193, B_194)) | ~v1_funct_1(k2_funct_2(A_193, B_194)) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_193, A_193))) | ~v3_funct_2(B_194, A_193, A_193) | ~v1_funct_2(B_194, A_193, A_193) | ~v1_funct_1(B_194))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1913])).
% 5.71/2.10  tff(c_1986, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1965])).
% 5.71/2.10  tff(c_2012, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_438, c_437, c_437, c_437, c_1986])).
% 5.71/2.10  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 5.71/2.10  tff(c_127, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 5.71/2.10  tff(c_439, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_127])).
% 5.71/2.10  tff(c_2013, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_439])).
% 5.71/2.10  tff(c_2020, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_65, c_2013])).
% 5.71/2.10  tff(c_2023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_326, c_414, c_366, c_2020])).
% 5.71/2.10  tff(c_2024, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 5.71/2.10  tff(c_2336, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2024])).
% 5.71/2.10  tff(c_2958, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_2336])).
% 5.71/2.10  tff(c_2965, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_2958])).
% 5.71/2.10  tff(c_2968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_64, c_2224, c_2292, c_2141, c_2965])).
% 5.71/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.71/2.10  
% 5.71/2.10  Inference rules
% 5.71/2.10  ----------------------
% 5.71/2.10  #Ref     : 0
% 5.71/2.10  #Sup     : 616
% 5.71/2.10  #Fact    : 0
% 5.71/2.10  #Define  : 0
% 5.71/2.10  #Split   : 3
% 5.71/2.10  #Chain   : 0
% 5.71/2.10  #Close   : 0
% 5.71/2.10  
% 5.71/2.10  Ordering : KBO
% 5.71/2.10  
% 5.71/2.10  Simplification rules
% 5.71/2.10  ----------------------
% 5.71/2.10  #Subsume      : 6
% 5.71/2.10  #Demod        : 1230
% 5.71/2.10  #Tautology    : 225
% 5.71/2.10  #SimpNegUnit  : 2
% 5.71/2.10  #BackRed      : 46
% 5.71/2.10  
% 5.71/2.10  #Partial instantiations: 0
% 5.71/2.10  #Strategies tried      : 1
% 5.71/2.10  
% 5.71/2.10  Timing (in seconds)
% 5.71/2.10  ----------------------
% 5.71/2.11  Preprocessing        : 0.33
% 5.71/2.11  Parsing              : 0.17
% 5.71/2.11  CNF conversion       : 0.02
% 5.71/2.11  Main loop            : 0.94
% 5.71/2.11  Inferencing          : 0.31
% 5.71/2.11  Reduction            : 0.37
% 5.71/2.11  Demodulation         : 0.29
% 5.71/2.11  BG Simplification    : 0.03
% 5.71/2.11  Subsumption          : 0.15
% 5.71/2.11  Abstraction          : 0.04
% 5.71/2.11  MUC search           : 0.00
% 5.71/2.11  Cooper               : 0.00
% 5.71/2.11  Total                : 1.31
% 5.71/2.11  Index Insertion      : 0.00
% 5.71/2.11  Index Deletion       : 0.00
% 5.71/2.11  Index Matching       : 0.00
% 5.71/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
