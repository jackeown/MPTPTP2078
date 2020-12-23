%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 6.13s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 351 expanded)
%              Number of leaves         :   42 ( 151 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 (1071 expanded)
%              Number of equality atoms :   40 (  86 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_106,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

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

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

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

tff(f_93,axiom,(
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

tff(c_2150,plain,(
    ! [C_204,A_205,B_206] :
      ( v1_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2158,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2150])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2360,plain,(
    ! [C_249,A_250,B_251] :
      ( v2_funct_1(C_249)
      | ~ v3_funct_2(C_249,A_250,B_251)
      | ~ v1_funct_1(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2369,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2360])).

tff(c_2376,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2369])).

tff(c_52,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_46,plain,(
    ! [A_23,B_24] : m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2397,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( r2_relset_1(A_260,B_261,C_262,C_262)
      | ~ m1_subset_1(D_263,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2407,plain,(
    ! [A_264,B_265,C_266] :
      ( r2_relset_1(A_264,B_265,C_266,C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2397])).

tff(c_2415,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_65,c_2407])).

tff(c_2166,plain,(
    ! [C_210,B_211,A_212] :
      ( v5_relat_1(C_210,B_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2179,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_2166])).

tff(c_2197,plain,(
    ! [B_219,A_220] :
      ( k2_relat_1(B_219) = A_220
      | ~ v2_funct_2(B_219,A_220)
      | ~ v5_relat_1(B_219,A_220)
      | ~ v1_relat_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2203,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2179,c_2197])).

tff(c_2212,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2203])).

tff(c_2233,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2212])).

tff(c_2291,plain,(
    ! [C_238,B_239,A_240] :
      ( v2_funct_2(C_238,B_239)
      | ~ v3_funct_2(C_238,A_240,B_239)
      | ~ v1_funct_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2300,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2291])).

tff(c_2307,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2300])).

tff(c_2309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2233,c_2307])).

tff(c_2310,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2212])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2475,plain,(
    ! [A_276,B_277] :
      ( k2_funct_2(A_276,B_277) = k2_funct_1(B_277)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1(A_276,A_276)))
      | ~ v3_funct_2(B_277,A_276,A_276)
      | ~ v1_funct_2(B_277,A_276,A_276)
      | ~ v1_funct_1(B_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2485,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2475])).

tff(c_2492,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2485])).

tff(c_2444,plain,(
    ! [A_273,B_274] :
      ( v1_funct_1(k2_funct_2(A_273,B_274))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k2_zfmisc_1(A_273,A_273)))
      | ~ v3_funct_2(B_274,A_273,A_273)
      | ~ v1_funct_2(B_274,A_273,A_273)
      | ~ v1_funct_1(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2454,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2444])).

tff(c_2461,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2454])).

tff(c_2493,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2461])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_funct_2(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2657,plain,(
    ! [E_296,A_293,B_292,D_291,C_295,F_294] :
      ( k1_partfun1(A_293,B_292,C_295,D_291,E_296,F_294) = k5_relat_1(E_296,F_294)
      | ~ m1_subset_1(F_294,k1_zfmisc_1(k2_zfmisc_1(C_295,D_291)))
      | ~ v1_funct_1(F_294)
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292)))
      | ~ v1_funct_1(E_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2667,plain,(
    ! [A_293,B_292,E_296] :
      ( k1_partfun1(A_293,B_292,'#skF_2','#skF_2',E_296,'#skF_3') = k5_relat_1(E_296,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(A_293,B_292)))
      | ~ v1_funct_1(E_296) ) ),
    inference(resolution,[status(thm)],[c_58,c_2657])).

tff(c_2690,plain,(
    ! [A_297,B_298,E_299] :
      ( k1_partfun1(A_297,B_298,'#skF_2','#skF_2',E_299,'#skF_3') = k5_relat_1(E_299,'#skF_3')
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298)))
      | ~ v1_funct_1(E_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2667])).

tff(c_2954,plain,(
    ! [A_305,B_306] :
      ( k1_partfun1(A_305,A_305,'#skF_2','#skF_2',k2_funct_2(A_305,B_306),'#skF_3') = k5_relat_1(k2_funct_2(A_305,B_306),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_305,B_306))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(k2_zfmisc_1(A_305,A_305)))
      | ~ v3_funct_2(B_306,A_305,A_305)
      | ~ v1_funct_2(B_306,A_305,A_305)
      | ~ v1_funct_1(B_306) ) ),
    inference(resolution,[status(thm)],[c_28,c_2690])).

tff(c_2969,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2954])).

tff(c_2986,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2493,c_2492,c_2492,c_2492,c_2969])).

tff(c_85,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_85])).

tff(c_294,plain,(
    ! [C_94,A_95,B_96] :
      ( v2_funct_1(C_94)
      | ~ v3_funct_2(C_94,A_95,B_96)
      | ~ v1_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_303,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_294])).

tff(c_310,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_303])).

tff(c_331,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( r2_relset_1(A_105,B_106,C_107,C_107)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_341,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_relset_1(A_109,B_110,C_111,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(resolution,[status(thm)],[c_46,c_331])).

tff(c_349,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_65,c_341])).

tff(c_150,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_150])).

tff(c_354,plain,(
    ! [A_116,B_117] :
      ( k1_relset_1(A_116,A_116,B_117) = A_116
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_zfmisc_1(A_116,A_116)))
      | ~ v1_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_364,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_354])).

tff(c_372,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_162,c_364])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4])).

tff(c_409,plain,(
    ! [A_121,B_122] :
      ( k2_funct_2(A_121,B_122) = k2_funct_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(A_121,A_121)))
      | ~ v3_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_419,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_409])).

tff(c_426,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_419])).

tff(c_378,plain,(
    ! [A_118,B_119] :
      ( v1_funct_1(k2_funct_2(A_118,B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_zfmisc_1(A_118,A_118)))
      | ~ v3_funct_2(B_119,A_118,A_118)
      | ~ v1_funct_2(B_119,A_118,A_118)
      | ~ v1_funct_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_388,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_378])).

tff(c_395,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_388])).

tff(c_427,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_395])).

tff(c_591,plain,(
    ! [D_137,A_139,C_141,B_138,E_142,F_140] :
      ( k1_partfun1(A_139,B_138,C_141,D_137,E_142,F_140) = k5_relat_1(E_142,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_141,D_137)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1985,plain,(
    ! [A_194,A_193,B_196,E_195,B_197] :
      ( k1_partfun1(A_193,B_197,A_194,A_194,E_195,k2_funct_2(A_194,B_196)) = k5_relat_1(E_195,k2_funct_2(A_194,B_196))
      | ~ v1_funct_1(k2_funct_2(A_194,B_196))
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_197)))
      | ~ v1_funct_1(E_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_196,A_194,A_194)
      | ~ v1_funct_2(B_196,A_194,A_194)
      | ~ v1_funct_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_28,c_591])).

tff(c_2005,plain,(
    ! [A_194,B_196] :
      ( k1_partfun1('#skF_2','#skF_2',A_194,A_194,'#skF_3',k2_funct_2(A_194,B_196)) = k5_relat_1('#skF_3',k2_funct_2(A_194,B_196))
      | ~ v1_funct_1(k2_funct_2(A_194,B_196))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_196,A_194,A_194)
      | ~ v1_funct_2(B_196,A_194,A_194)
      | ~ v1_funct_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_58,c_1985])).

tff(c_2080,plain,(
    ! [A_198,B_199] :
      ( k1_partfun1('#skF_2','#skF_2',A_198,A_198,'#skF_3',k2_funct_2(A_198,B_199)) = k5_relat_1('#skF_3',k2_funct_2(A_198,B_199))
      | ~ v1_funct_1(k2_funct_2(A_198,B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2005])).

tff(c_2101,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2080])).

tff(c_2127,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_427,c_426,c_426,c_426,c_2101])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_81,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_428,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_81])).

tff(c_2135,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2127,c_428])).

tff(c_2142,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2135])).

tff(c_2145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_310,c_349,c_372,c_2142])).

tff(c_2146,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2494,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2146])).

tff(c_3046,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2986,c_2494])).

tff(c_3053,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_3046])).

tff(c_3056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_64,c_2376,c_2415,c_2310,c_3053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.13/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.18  
% 6.34/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.18  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.34/2.18  
% 6.34/2.18  %Foreground sorts:
% 6.34/2.18  
% 6.34/2.18  
% 6.34/2.18  %Background operators:
% 6.34/2.18  
% 6.34/2.18  
% 6.34/2.18  %Foreground operators:
% 6.34/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.34/2.18  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.34/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.34/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.34/2.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.34/2.18  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.34/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.34/2.18  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.34/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.18  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.34/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.34/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.34/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.34/2.18  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.34/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.34/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.34/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.34/2.18  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.34/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.34/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.34/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.18  
% 6.34/2.21  tff(f_149, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.34/2.21  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.34/2.21  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.34/2.21  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.34/2.21  tff(f_57, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.34/2.21  tff(f_106, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 6.34/2.21  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.34/2.21  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.34/2.21  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.34/2.21  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.34/2.21  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.34/2.21  tff(f_93, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.34/2.21  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.34/2.21  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.34/2.21  tff(f_136, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.34/2.21  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.34/2.21  tff(c_2150, plain, (![C_204, A_205, B_206]: (v1_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.34/2.21  tff(c_2158, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2150])).
% 6.34/2.21  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.34/2.21  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.34/2.21  tff(c_2360, plain, (![C_249, A_250, B_251]: (v2_funct_1(C_249) | ~v3_funct_2(C_249, A_250, B_251) | ~v1_funct_1(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.34/2.21  tff(c_2369, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2360])).
% 6.34/2.21  tff(c_2376, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2369])).
% 6.34/2.21  tff(c_52, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.34/2.21  tff(c_16, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.34/2.21  tff(c_65, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 6.34/2.21  tff(c_46, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.34/2.21  tff(c_2397, plain, (![A_260, B_261, C_262, D_263]: (r2_relset_1(A_260, B_261, C_262, C_262) | ~m1_subset_1(D_263, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.34/2.21  tff(c_2407, plain, (![A_264, B_265, C_266]: (r2_relset_1(A_264, B_265, C_266, C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(resolution, [status(thm)], [c_46, c_2397])).
% 6.34/2.21  tff(c_2415, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_65, c_2407])).
% 6.34/2.21  tff(c_2166, plain, (![C_210, B_211, A_212]: (v5_relat_1(C_210, B_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.34/2.21  tff(c_2179, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_2166])).
% 6.34/2.21  tff(c_2197, plain, (![B_219, A_220]: (k2_relat_1(B_219)=A_220 | ~v2_funct_2(B_219, A_220) | ~v5_relat_1(B_219, A_220) | ~v1_relat_1(B_219))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.34/2.21  tff(c_2203, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2179, c_2197])).
% 6.34/2.21  tff(c_2212, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2203])).
% 6.34/2.21  tff(c_2233, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2212])).
% 6.34/2.21  tff(c_2291, plain, (![C_238, B_239, A_240]: (v2_funct_2(C_238, B_239) | ~v3_funct_2(C_238, A_240, B_239) | ~v1_funct_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.34/2.21  tff(c_2300, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2291])).
% 6.34/2.21  tff(c_2307, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2300])).
% 6.34/2.21  tff(c_2309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2233, c_2307])).
% 6.34/2.21  tff(c_2310, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2212])).
% 6.34/2.21  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.34/2.21  tff(c_67, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2])).
% 6.34/2.21  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.34/2.21  tff(c_2475, plain, (![A_276, B_277]: (k2_funct_2(A_276, B_277)=k2_funct_1(B_277) | ~m1_subset_1(B_277, k1_zfmisc_1(k2_zfmisc_1(A_276, A_276))) | ~v3_funct_2(B_277, A_276, A_276) | ~v1_funct_2(B_277, A_276, A_276) | ~v1_funct_1(B_277))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.34/2.21  tff(c_2485, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2475])).
% 6.34/2.21  tff(c_2492, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2485])).
% 6.34/2.21  tff(c_2444, plain, (![A_273, B_274]: (v1_funct_1(k2_funct_2(A_273, B_274)) | ~m1_subset_1(B_274, k1_zfmisc_1(k2_zfmisc_1(A_273, A_273))) | ~v3_funct_2(B_274, A_273, A_273) | ~v1_funct_2(B_274, A_273, A_273) | ~v1_funct_1(B_274))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.34/2.21  tff(c_2454, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2444])).
% 6.34/2.21  tff(c_2461, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2454])).
% 6.34/2.21  tff(c_2493, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2461])).
% 6.34/2.21  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(k2_funct_2(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.34/2.21  tff(c_2657, plain, (![E_296, A_293, B_292, D_291, C_295, F_294]: (k1_partfun1(A_293, B_292, C_295, D_291, E_296, F_294)=k5_relat_1(E_296, F_294) | ~m1_subset_1(F_294, k1_zfmisc_1(k2_zfmisc_1(C_295, D_291))) | ~v1_funct_1(F_294) | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))) | ~v1_funct_1(E_296))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.34/2.21  tff(c_2667, plain, (![A_293, B_292, E_296]: (k1_partfun1(A_293, B_292, '#skF_2', '#skF_2', E_296, '#skF_3')=k5_relat_1(E_296, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(A_293, B_292))) | ~v1_funct_1(E_296))), inference(resolution, [status(thm)], [c_58, c_2657])).
% 6.34/2.21  tff(c_2690, plain, (![A_297, B_298, E_299]: (k1_partfun1(A_297, B_298, '#skF_2', '#skF_2', E_299, '#skF_3')=k5_relat_1(E_299, '#skF_3') | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))) | ~v1_funct_1(E_299))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2667])).
% 6.34/2.21  tff(c_2954, plain, (![A_305, B_306]: (k1_partfun1(A_305, A_305, '#skF_2', '#skF_2', k2_funct_2(A_305, B_306), '#skF_3')=k5_relat_1(k2_funct_2(A_305, B_306), '#skF_3') | ~v1_funct_1(k2_funct_2(A_305, B_306)) | ~m1_subset_1(B_306, k1_zfmisc_1(k2_zfmisc_1(A_305, A_305))) | ~v3_funct_2(B_306, A_305, A_305) | ~v1_funct_2(B_306, A_305, A_305) | ~v1_funct_1(B_306))), inference(resolution, [status(thm)], [c_28, c_2690])).
% 6.34/2.21  tff(c_2969, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2954])).
% 6.34/2.21  tff(c_2986, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2493, c_2492, c_2492, c_2492, c_2969])).
% 6.34/2.21  tff(c_85, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.34/2.21  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_85])).
% 6.34/2.21  tff(c_294, plain, (![C_94, A_95, B_96]: (v2_funct_1(C_94) | ~v3_funct_2(C_94, A_95, B_96) | ~v1_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.34/2.21  tff(c_303, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_294])).
% 6.34/2.21  tff(c_310, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_303])).
% 6.34/2.21  tff(c_331, plain, (![A_105, B_106, C_107, D_108]: (r2_relset_1(A_105, B_106, C_107, C_107) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.34/2.21  tff(c_341, plain, (![A_109, B_110, C_111]: (r2_relset_1(A_109, B_110, C_111, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(resolution, [status(thm)], [c_46, c_331])).
% 6.34/2.21  tff(c_349, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_65, c_341])).
% 6.34/2.21  tff(c_150, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.34/2.21  tff(c_162, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_150])).
% 6.34/2.21  tff(c_354, plain, (![A_116, B_117]: (k1_relset_1(A_116, A_116, B_117)=A_116 | ~m1_subset_1(B_117, k1_zfmisc_1(k2_zfmisc_1(A_116, A_116))) | ~v1_funct_2(B_117, A_116, A_116) | ~v1_funct_1(B_117))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.34/2.21  tff(c_364, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_354])).
% 6.34/2.21  tff(c_372, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_162, c_364])).
% 6.34/2.21  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.34/2.21  tff(c_66, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4])).
% 6.34/2.21  tff(c_409, plain, (![A_121, B_122]: (k2_funct_2(A_121, B_122)=k2_funct_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1(A_121, A_121))) | ~v3_funct_2(B_122, A_121, A_121) | ~v1_funct_2(B_122, A_121, A_121) | ~v1_funct_1(B_122))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.34/2.21  tff(c_419, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_409])).
% 6.34/2.21  tff(c_426, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_419])).
% 6.34/2.21  tff(c_378, plain, (![A_118, B_119]: (v1_funct_1(k2_funct_2(A_118, B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_zfmisc_1(A_118, A_118))) | ~v3_funct_2(B_119, A_118, A_118) | ~v1_funct_2(B_119, A_118, A_118) | ~v1_funct_1(B_119))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.34/2.21  tff(c_388, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_378])).
% 6.34/2.21  tff(c_395, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_388])).
% 6.34/2.21  tff(c_427, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_395])).
% 6.34/2.21  tff(c_591, plain, (![D_137, A_139, C_141, B_138, E_142, F_140]: (k1_partfun1(A_139, B_138, C_141, D_137, E_142, F_140)=k5_relat_1(E_142, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_141, D_137))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_142))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.34/2.21  tff(c_1985, plain, (![A_194, A_193, B_196, E_195, B_197]: (k1_partfun1(A_193, B_197, A_194, A_194, E_195, k2_funct_2(A_194, B_196))=k5_relat_1(E_195, k2_funct_2(A_194, B_196)) | ~v1_funct_1(k2_funct_2(A_194, B_196)) | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_197))) | ~v1_funct_1(E_195) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_196, A_194, A_194) | ~v1_funct_2(B_196, A_194, A_194) | ~v1_funct_1(B_196))), inference(resolution, [status(thm)], [c_28, c_591])).
% 6.34/2.21  tff(c_2005, plain, (![A_194, B_196]: (k1_partfun1('#skF_2', '#skF_2', A_194, A_194, '#skF_3', k2_funct_2(A_194, B_196))=k5_relat_1('#skF_3', k2_funct_2(A_194, B_196)) | ~v1_funct_1(k2_funct_2(A_194, B_196)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_196, A_194, A_194) | ~v1_funct_2(B_196, A_194, A_194) | ~v1_funct_1(B_196))), inference(resolution, [status(thm)], [c_58, c_1985])).
% 6.34/2.21  tff(c_2080, plain, (![A_198, B_199]: (k1_partfun1('#skF_2', '#skF_2', A_198, A_198, '#skF_3', k2_funct_2(A_198, B_199))=k5_relat_1('#skF_3', k2_funct_2(A_198, B_199)) | ~v1_funct_1(k2_funct_2(A_198, B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2005])).
% 6.34/2.21  tff(c_2101, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2080])).
% 6.34/2.21  tff(c_2127, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_427, c_426, c_426, c_426, c_2101])).
% 6.34/2.21  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.34/2.21  tff(c_81, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 6.34/2.21  tff(c_428, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_81])).
% 6.34/2.21  tff(c_2135, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2127, c_428])).
% 6.34/2.21  tff(c_2142, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_66, c_2135])).
% 6.34/2.21  tff(c_2145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_310, c_349, c_372, c_2142])).
% 6.34/2.21  tff(c_2146, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 6.34/2.21  tff(c_2494, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2146])).
% 6.34/2.21  tff(c_3046, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2986, c_2494])).
% 6.34/2.21  tff(c_3053, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_3046])).
% 6.34/2.21  tff(c_3056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2158, c_64, c_2376, c_2415, c_2310, c_3053])).
% 6.34/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.21  
% 6.34/2.21  Inference rules
% 6.34/2.21  ----------------------
% 6.34/2.21  #Ref     : 0
% 6.34/2.21  #Sup     : 636
% 6.34/2.21  #Fact    : 0
% 6.34/2.21  #Define  : 0
% 6.34/2.21  #Split   : 3
% 6.34/2.21  #Chain   : 0
% 6.34/2.21  #Close   : 0
% 6.34/2.21  
% 6.34/2.21  Ordering : KBO
% 6.34/2.21  
% 6.34/2.21  Simplification rules
% 6.34/2.21  ----------------------
% 6.34/2.21  #Subsume      : 6
% 6.34/2.21  #Demod        : 1426
% 6.34/2.21  #Tautology    : 248
% 6.34/2.21  #SimpNegUnit  : 2
% 6.34/2.21  #BackRed      : 53
% 6.34/2.21  
% 6.34/2.21  #Partial instantiations: 0
% 6.34/2.21  #Strategies tried      : 1
% 6.34/2.21  
% 6.34/2.21  Timing (in seconds)
% 6.34/2.21  ----------------------
% 6.34/2.21  Preprocessing        : 0.36
% 6.34/2.21  Parsing              : 0.19
% 6.34/2.21  CNF conversion       : 0.02
% 6.34/2.21  Main loop            : 1.06
% 6.34/2.21  Inferencing          : 0.35
% 6.34/2.21  Reduction            : 0.43
% 6.34/2.21  Demodulation         : 0.33
% 6.34/2.21  BG Simplification    : 0.03
% 6.34/2.21  Subsumption          : 0.17
% 6.34/2.21  Abstraction          : 0.04
% 6.34/2.21  MUC search           : 0.00
% 6.34/2.21  Cooper               : 0.00
% 6.34/2.21  Total                : 1.47
% 6.34/2.21  Index Insertion      : 0.00
% 6.34/2.21  Index Deletion       : 0.00
% 6.34/2.21  Index Matching       : 0.00
% 6.34/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
