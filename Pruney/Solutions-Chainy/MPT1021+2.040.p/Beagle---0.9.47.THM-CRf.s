%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 351 expanded)
%              Number of leaves         :   42 ( 151 expanded)
%              Depth                    :    9
%              Number of atoms          :  273 (1069 expanded)
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

tff(f_147,negated_conjecture,(
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

tff(f_126,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_104,axiom,(
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

tff(f_124,axiom,(
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

tff(f_114,axiom,(
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

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2039,plain,(
    ! [C_196,A_197,B_198] :
      ( v1_relat_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2052,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2039])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2263,plain,(
    ! [C_239,A_240,B_241] :
      ( v2_funct_1(C_239)
      | ~ v3_funct_2(C_239,A_240,B_241)
      | ~ v1_funct_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2272,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2263])).

tff(c_2279,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2272])).

tff(c_50,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    ! [A_15] : m1_subset_1(k6_partfun1(A_15),k1_zfmisc_1(k2_zfmisc_1(A_15,A_15))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_44,plain,(
    ! [A_23,B_24] : m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2301,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( r2_relset_1(A_251,B_252,C_253,C_253)
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2311,plain,(
    ! [A_255,B_256,C_257] :
      ( r2_relset_1(A_255,B_256,C_257,C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(resolution,[status(thm)],[c_44,c_2301])).

tff(c_2319,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_63,c_2311])).

tff(c_2053,plain,(
    ! [C_199,B_200,A_201] :
      ( v5_relat_1(C_199,B_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_201,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2066,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2053])).

tff(c_2085,plain,(
    ! [B_209,A_210] :
      ( k2_relat_1(B_209) = A_210
      | ~ v2_funct_2(B_209,A_210)
      | ~ v5_relat_1(B_209,A_210)
      | ~ v1_relat_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2091,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2066,c_2085])).

tff(c_2100,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_2091])).

tff(c_2104,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2100])).

tff(c_2177,plain,(
    ! [C_225,B_226,A_227] :
      ( v2_funct_2(C_225,B_226)
      | ~ v3_funct_2(C_225,A_227,B_226)
      | ~ v1_funct_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2186,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2177])).

tff(c_2193,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2186])).

tff(c_2195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2104,c_2193])).

tff(c_2196,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2100])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2373,plain,(
    ! [A_269,B_270] :
      ( k2_funct_2(A_269,B_270) = k2_funct_1(B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(k2_zfmisc_1(A_269,A_269)))
      | ~ v3_funct_2(B_270,A_269,A_269)
      | ~ v1_funct_2(B_270,A_269,A_269)
      | ~ v1_funct_1(B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2383,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2373])).

tff(c_2390,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2383])).

tff(c_2351,plain,(
    ! [A_263,B_264] :
      ( v1_funct_1(k2_funct_2(A_263,B_264))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(k2_zfmisc_1(A_263,A_263)))
      | ~ v3_funct_2(B_264,A_263,A_263)
      | ~ v1_funct_2(B_264,A_263,A_263)
      | ~ v1_funct_1(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2361,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2351])).

tff(c_2368,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2361])).

tff(c_2391,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_2368])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_funct_2(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k2_zfmisc_1(A_21,A_21)))
      | ~ v3_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_2(B_22,A_21,A_21)
      | ~ v1_funct_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2543,plain,(
    ! [F_285,E_287,A_284,B_283,C_286,D_282] :
      ( k1_partfun1(A_284,B_283,C_286,D_282,E_287,F_285) = k5_relat_1(E_287,F_285)
      | ~ m1_subset_1(F_285,k1_zfmisc_1(k2_zfmisc_1(C_286,D_282)))
      | ~ v1_funct_1(F_285)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_284,B_283)))
      | ~ v1_funct_1(E_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2553,plain,(
    ! [A_284,B_283,E_287] :
      ( k1_partfun1(A_284,B_283,'#skF_2','#skF_2',E_287,'#skF_3') = k5_relat_1(E_287,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_284,B_283)))
      | ~ v1_funct_1(E_287) ) ),
    inference(resolution,[status(thm)],[c_56,c_2543])).

tff(c_2580,plain,(
    ! [A_288,B_289,E_290] :
      ( k1_partfun1(A_288,B_289,'#skF_2','#skF_2',E_290,'#skF_3') = k5_relat_1(E_290,'#skF_3')
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289)))
      | ~ v1_funct_1(E_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2553])).

tff(c_2812,plain,(
    ! [A_297,B_298] :
      ( k1_partfun1(A_297,A_297,'#skF_2','#skF_2',k2_funct_2(A_297,B_298),'#skF_3') = k5_relat_1(k2_funct_2(A_297,B_298),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_297,B_298))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(k2_zfmisc_1(A_297,A_297)))
      | ~ v3_funct_2(B_298,A_297,A_297)
      | ~ v1_funct_2(B_298,A_297,A_297)
      | ~ v1_funct_1(B_298) ) ),
    inference(resolution,[status(thm)],[c_28,c_2580])).

tff(c_2825,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2812])).

tff(c_2839,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2391,c_2390,c_2390,c_2390,c_2825])).

tff(c_82,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_82])).

tff(c_306,plain,(
    ! [C_92,A_93,B_94] :
      ( v2_funct_1(C_92)
      | ~ v3_funct_2(C_92,A_93,B_94)
      | ~ v1_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_315,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_306])).

tff(c_322,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_315])).

tff(c_373,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( r2_relset_1(A_107,B_108,C_109,C_109)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_383,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_relset_1(A_111,B_112,C_113,C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(resolution,[status(thm)],[c_44,c_373])).

tff(c_391,plain,(
    ! [A_15] : r2_relset_1(A_15,A_15,k6_partfun1(A_15),k6_partfun1(A_15)) ),
    inference(resolution,[status(thm)],[c_63,c_383])).

tff(c_253,plain,(
    ! [A_84,B_85,C_86] :
      ( k1_relset_1(A_84,B_85,C_86) = k1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_265,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_253])).

tff(c_344,plain,(
    ! [A_104,B_105] :
      ( k1_relset_1(A_104,A_104,B_105) = A_104
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_zfmisc_1(A_104,A_104)))
      | ~ v1_funct_2(B_105,A_104,A_104)
      | ~ v1_funct_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_354,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_344])).

tff(c_362,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_265,c_354])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4])).

tff(c_414,plain,(
    ! [A_120,B_121] :
      ( k2_funct_2(A_120,B_121) = k2_funct_1(B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_zfmisc_1(A_120,A_120)))
      | ~ v3_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_424,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_414])).

tff(c_431,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_424])).

tff(c_395,plain,(
    ! [A_117,B_118] :
      ( v1_funct_1(k2_funct_2(A_117,B_118))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v3_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_405,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_395])).

tff(c_412,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_405])).

tff(c_432,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_412])).

tff(c_596,plain,(
    ! [B_137,C_140,A_138,F_139,D_136,E_141] :
      ( k1_partfun1(A_138,B_137,C_140,D_136,E_141,F_139) = k5_relat_1(E_141,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_136)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1915,plain,(
    ! [B_188,A_187,B_190,A_186,E_189] :
      ( k1_partfun1(A_187,B_190,A_186,A_186,E_189,k2_funct_2(A_186,B_188)) = k5_relat_1(E_189,k2_funct_2(A_186,B_188))
      | ~ v1_funct_1(k2_funct_2(A_186,B_188))
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_190)))
      | ~ v1_funct_1(E_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_188,A_186,A_186)
      | ~ v1_funct_2(B_188,A_186,A_186)
      | ~ v1_funct_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_28,c_596])).

tff(c_1935,plain,(
    ! [A_186,B_188] :
      ( k1_partfun1('#skF_2','#skF_2',A_186,A_186,'#skF_3',k2_funct_2(A_186,B_188)) = k5_relat_1('#skF_3',k2_funct_2(A_186,B_188))
      | ~ v1_funct_1(k2_funct_2(A_186,B_188))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v3_funct_2(B_188,A_186,A_186)
      | ~ v1_funct_2(B_188,A_186,A_186)
      | ~ v1_funct_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_56,c_1915])).

tff(c_1976,plain,(
    ! [A_191,B_192] :
      ( k1_partfun1('#skF_2','#skF_2',A_191,A_191,'#skF_3',k2_funct_2(A_191,B_192)) = k5_relat_1('#skF_3',k2_funct_2(A_191,B_192))
      | ~ v1_funct_1(k2_funct_2(A_191,B_192))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191)))
      | ~ v3_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_1(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1935])).

tff(c_1997,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1976])).

tff(c_2023,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_432,c_431,c_431,c_431,c_1997])).

tff(c_54,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_79,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_433,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_79])).

tff(c_2024,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_433])).

tff(c_2031,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2024])).

tff(c_2034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_62,c_322,c_391,c_362,c_2031])).

tff(c_2035,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2393,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2390,c_2035])).

tff(c_2976,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2839,c_2393])).

tff(c_3025,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2976])).

tff(c_3028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_62,c_2279,c_2319,c_2196,c_3025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.10  
% 5.77/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.10  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.77/2.10  
% 5.77/2.10  %Foreground sorts:
% 5.77/2.10  
% 5.77/2.10  
% 5.77/2.10  %Background operators:
% 5.77/2.10  
% 5.77/2.10  
% 5.77/2.10  %Foreground operators:
% 5.77/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.77/2.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.77/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.77/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.77/2.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.77/2.10  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.77/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.77/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.77/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.77/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.10  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.77/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.77/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.77/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.77/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.77/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.77/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.77/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.77/2.10  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.77/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.77/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.77/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.10  
% 5.92/2.12  tff(f_147, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.92/2.12  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.92/2.12  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.92/2.12  tff(f_126, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.92/2.12  tff(f_57, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.92/2.12  tff(f_104, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_partfun1)).
% 5.92/2.12  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.92/2.12  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.92/2.12  tff(f_77, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.92/2.12  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.92/2.12  tff(f_124, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.92/2.12  tff(f_93, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.92/2.12  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.92/2.12  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.92/2.12  tff(f_134, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.92/2.12  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.92/2.12  tff(c_2039, plain, (![C_196, A_197, B_198]: (v1_relat_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.92/2.12  tff(c_2052, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2039])).
% 5.92/2.12  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.92/2.12  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.92/2.12  tff(c_2263, plain, (![C_239, A_240, B_241]: (v2_funct_1(C_239) | ~v3_funct_2(C_239, A_240, B_241) | ~v1_funct_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.92/2.12  tff(c_2272, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2263])).
% 5.92/2.12  tff(c_2279, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2272])).
% 5.92/2.12  tff(c_50, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.92/2.12  tff(c_16, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.92/2.12  tff(c_63, plain, (![A_15]: (m1_subset_1(k6_partfun1(A_15), k1_zfmisc_1(k2_zfmisc_1(A_15, A_15))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 5.92/2.12  tff(c_44, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.92/2.12  tff(c_2301, plain, (![A_251, B_252, C_253, D_254]: (r2_relset_1(A_251, B_252, C_253, C_253) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.92/2.12  tff(c_2311, plain, (![A_255, B_256, C_257]: (r2_relset_1(A_255, B_256, C_257, C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(resolution, [status(thm)], [c_44, c_2301])).
% 5.92/2.12  tff(c_2319, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_63, c_2311])).
% 5.92/2.12  tff(c_2053, plain, (![C_199, B_200, A_201]: (v5_relat_1(C_199, B_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_201, B_200))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.12  tff(c_2066, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_2053])).
% 5.92/2.12  tff(c_2085, plain, (![B_209, A_210]: (k2_relat_1(B_209)=A_210 | ~v2_funct_2(B_209, A_210) | ~v5_relat_1(B_209, A_210) | ~v1_relat_1(B_209))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.92/2.12  tff(c_2091, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2066, c_2085])).
% 5.92/2.12  tff(c_2100, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_2091])).
% 5.92/2.12  tff(c_2104, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2100])).
% 5.92/2.12  tff(c_2177, plain, (![C_225, B_226, A_227]: (v2_funct_2(C_225, B_226) | ~v3_funct_2(C_225, A_227, B_226) | ~v1_funct_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.92/2.12  tff(c_2186, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2177])).
% 5.92/2.12  tff(c_2193, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2186])).
% 5.92/2.12  tff(c_2195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2104, c_2193])).
% 5.92/2.12  tff(c_2196, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2100])).
% 5.92/2.12  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.92/2.12  tff(c_65, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2])).
% 5.92/2.12  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.92/2.12  tff(c_2373, plain, (![A_269, B_270]: (k2_funct_2(A_269, B_270)=k2_funct_1(B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(k2_zfmisc_1(A_269, A_269))) | ~v3_funct_2(B_270, A_269, A_269) | ~v1_funct_2(B_270, A_269, A_269) | ~v1_funct_1(B_270))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.92/2.12  tff(c_2383, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2373])).
% 5.92/2.12  tff(c_2390, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2383])).
% 5.92/2.12  tff(c_2351, plain, (![A_263, B_264]: (v1_funct_1(k2_funct_2(A_263, B_264)) | ~m1_subset_1(B_264, k1_zfmisc_1(k2_zfmisc_1(A_263, A_263))) | ~v3_funct_2(B_264, A_263, A_263) | ~v1_funct_2(B_264, A_263, A_263) | ~v1_funct_1(B_264))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.92/2.12  tff(c_2361, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2351])).
% 5.92/2.12  tff(c_2368, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2361])).
% 5.92/2.12  tff(c_2391, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_2368])).
% 5.92/2.12  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(k2_funct_2(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))) | ~v3_funct_2(B_22, A_21, A_21) | ~v1_funct_2(B_22, A_21, A_21) | ~v1_funct_1(B_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.92/2.12  tff(c_2543, plain, (![F_285, E_287, A_284, B_283, C_286, D_282]: (k1_partfun1(A_284, B_283, C_286, D_282, E_287, F_285)=k5_relat_1(E_287, F_285) | ~m1_subset_1(F_285, k1_zfmisc_1(k2_zfmisc_1(C_286, D_282))) | ~v1_funct_1(F_285) | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_284, B_283))) | ~v1_funct_1(E_287))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.92/2.12  tff(c_2553, plain, (![A_284, B_283, E_287]: (k1_partfun1(A_284, B_283, '#skF_2', '#skF_2', E_287, '#skF_3')=k5_relat_1(E_287, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_284, B_283))) | ~v1_funct_1(E_287))), inference(resolution, [status(thm)], [c_56, c_2543])).
% 5.92/2.12  tff(c_2580, plain, (![A_288, B_289, E_290]: (k1_partfun1(A_288, B_289, '#skF_2', '#skF_2', E_290, '#skF_3')=k5_relat_1(E_290, '#skF_3') | ~m1_subset_1(E_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))) | ~v1_funct_1(E_290))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2553])).
% 5.92/2.12  tff(c_2812, plain, (![A_297, B_298]: (k1_partfun1(A_297, A_297, '#skF_2', '#skF_2', k2_funct_2(A_297, B_298), '#skF_3')=k5_relat_1(k2_funct_2(A_297, B_298), '#skF_3') | ~v1_funct_1(k2_funct_2(A_297, B_298)) | ~m1_subset_1(B_298, k1_zfmisc_1(k2_zfmisc_1(A_297, A_297))) | ~v3_funct_2(B_298, A_297, A_297) | ~v1_funct_2(B_298, A_297, A_297) | ~v1_funct_1(B_298))), inference(resolution, [status(thm)], [c_28, c_2580])).
% 5.92/2.12  tff(c_2825, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2812])).
% 5.92/2.12  tff(c_2839, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2391, c_2390, c_2390, c_2390, c_2825])).
% 5.92/2.12  tff(c_82, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.92/2.12  tff(c_95, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_82])).
% 5.92/2.12  tff(c_306, plain, (![C_92, A_93, B_94]: (v2_funct_1(C_92) | ~v3_funct_2(C_92, A_93, B_94) | ~v1_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.92/2.12  tff(c_315, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_306])).
% 5.92/2.12  tff(c_322, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_315])).
% 5.92/2.12  tff(c_373, plain, (![A_107, B_108, C_109, D_110]: (r2_relset_1(A_107, B_108, C_109, C_109) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.92/2.12  tff(c_383, plain, (![A_111, B_112, C_113]: (r2_relset_1(A_111, B_112, C_113, C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(resolution, [status(thm)], [c_44, c_373])).
% 5.92/2.12  tff(c_391, plain, (![A_15]: (r2_relset_1(A_15, A_15, k6_partfun1(A_15), k6_partfun1(A_15)))), inference(resolution, [status(thm)], [c_63, c_383])).
% 5.92/2.12  tff(c_253, plain, (![A_84, B_85, C_86]: (k1_relset_1(A_84, B_85, C_86)=k1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.92/2.12  tff(c_265, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_253])).
% 5.92/2.12  tff(c_344, plain, (![A_104, B_105]: (k1_relset_1(A_104, A_104, B_105)=A_104 | ~m1_subset_1(B_105, k1_zfmisc_1(k2_zfmisc_1(A_104, A_104))) | ~v1_funct_2(B_105, A_104, A_104) | ~v1_funct_1(B_105))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.92/2.12  tff(c_354, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_344])).
% 5.92/2.12  tff(c_362, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_265, c_354])).
% 5.92/2.12  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.92/2.12  tff(c_64, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4])).
% 5.92/2.12  tff(c_414, plain, (![A_120, B_121]: (k2_funct_2(A_120, B_121)=k2_funct_1(B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(k2_zfmisc_1(A_120, A_120))) | ~v3_funct_2(B_121, A_120, A_120) | ~v1_funct_2(B_121, A_120, A_120) | ~v1_funct_1(B_121))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.92/2.12  tff(c_424, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_414])).
% 5.92/2.12  tff(c_431, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_424])).
% 5.92/2.12  tff(c_395, plain, (![A_117, B_118]: (v1_funct_1(k2_funct_2(A_117, B_118)) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v3_funct_2(B_118, A_117, A_117) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.92/2.12  tff(c_405, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_395])).
% 5.92/2.12  tff(c_412, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_405])).
% 5.92/2.12  tff(c_432, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_412])).
% 5.92/2.12  tff(c_596, plain, (![B_137, C_140, A_138, F_139, D_136, E_141]: (k1_partfun1(A_138, B_137, C_140, D_136, E_141, F_139)=k5_relat_1(E_141, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_136))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.92/2.12  tff(c_1915, plain, (![B_188, A_187, B_190, A_186, E_189]: (k1_partfun1(A_187, B_190, A_186, A_186, E_189, k2_funct_2(A_186, B_188))=k5_relat_1(E_189, k2_funct_2(A_186, B_188)) | ~v1_funct_1(k2_funct_2(A_186, B_188)) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_190))) | ~v1_funct_1(E_189) | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_188, A_186, A_186) | ~v1_funct_2(B_188, A_186, A_186) | ~v1_funct_1(B_188))), inference(resolution, [status(thm)], [c_28, c_596])).
% 5.92/2.12  tff(c_1935, plain, (![A_186, B_188]: (k1_partfun1('#skF_2', '#skF_2', A_186, A_186, '#skF_3', k2_funct_2(A_186, B_188))=k5_relat_1('#skF_3', k2_funct_2(A_186, B_188)) | ~v1_funct_1(k2_funct_2(A_186, B_188)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_188, k1_zfmisc_1(k2_zfmisc_1(A_186, A_186))) | ~v3_funct_2(B_188, A_186, A_186) | ~v1_funct_2(B_188, A_186, A_186) | ~v1_funct_1(B_188))), inference(resolution, [status(thm)], [c_56, c_1915])).
% 5.92/2.12  tff(c_1976, plain, (![A_191, B_192]: (k1_partfun1('#skF_2', '#skF_2', A_191, A_191, '#skF_3', k2_funct_2(A_191, B_192))=k5_relat_1('#skF_3', k2_funct_2(A_191, B_192)) | ~v1_funct_1(k2_funct_2(A_191, B_192)) | ~m1_subset_1(B_192, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))) | ~v3_funct_2(B_192, A_191, A_191) | ~v1_funct_2(B_192, A_191, A_191) | ~v1_funct_1(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1935])).
% 5.92/2.12  tff(c_1997, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1976])).
% 5.92/2.12  tff(c_2023, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_432, c_431, c_431, c_431, c_1997])).
% 5.92/2.12  tff(c_54, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.92/2.12  tff(c_79, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.92/2.12  tff(c_433, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_79])).
% 5.92/2.12  tff(c_2024, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2023, c_433])).
% 5.92/2.12  tff(c_2031, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_2024])).
% 5.92/2.12  tff(c_2034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_62, c_322, c_391, c_362, c_2031])).
% 5.92/2.12  tff(c_2035, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 5.92/2.12  tff(c_2393, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2390, c_2035])).
% 5.92/2.12  tff(c_2976, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2839, c_2393])).
% 5.92/2.12  tff(c_3025, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_65, c_2976])).
% 5.92/2.12  tff(c_3028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2052, c_62, c_2279, c_2319, c_2196, c_3025])).
% 5.92/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.12  
% 5.92/2.12  Inference rules
% 5.92/2.12  ----------------------
% 5.92/2.12  #Ref     : 0
% 5.92/2.12  #Sup     : 631
% 5.92/2.12  #Fact    : 0
% 5.92/2.12  #Define  : 0
% 5.92/2.12  #Split   : 3
% 5.92/2.12  #Chain   : 0
% 5.92/2.12  #Close   : 0
% 5.92/2.12  
% 5.92/2.12  Ordering : KBO
% 5.92/2.12  
% 5.92/2.12  Simplification rules
% 5.92/2.12  ----------------------
% 5.92/2.12  #Subsume      : 6
% 5.92/2.12  #Demod        : 1245
% 5.92/2.12  #Tautology    : 237
% 5.92/2.12  #SimpNegUnit  : 2
% 5.92/2.12  #BackRed      : 46
% 5.92/2.12  
% 5.92/2.12  #Partial instantiations: 0
% 5.92/2.12  #Strategies tried      : 1
% 5.92/2.12  
% 5.92/2.12  Timing (in seconds)
% 5.92/2.12  ----------------------
% 5.97/2.13  Preprocessing        : 0.34
% 5.97/2.13  Parsing              : 0.18
% 5.97/2.13  CNF conversion       : 0.02
% 5.97/2.13  Main loop            : 0.95
% 5.97/2.13  Inferencing          : 0.33
% 5.97/2.13  Reduction            : 0.36
% 5.97/2.13  Demodulation         : 0.28
% 5.97/2.13  BG Simplification    : 0.03
% 5.97/2.13  Subsumption          : 0.15
% 5.97/2.13  Abstraction          : 0.04
% 5.97/2.13  MUC search           : 0.00
% 5.97/2.13  Cooper               : 0.00
% 5.97/2.13  Total                : 1.33
% 5.97/2.13  Index Insertion      : 0.00
% 5.97/2.13  Index Deletion       : 0.00
% 5.97/2.13  Index Matching       : 0.00
% 5.97/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
