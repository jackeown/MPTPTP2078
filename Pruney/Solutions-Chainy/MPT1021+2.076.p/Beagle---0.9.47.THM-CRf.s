%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 369 expanded)
%              Number of leaves         :   42 ( 157 expanded)
%              Depth                    :    9
%              Number of atoms          :  270 (1091 expanded)
%              Number of equality atoms :   40 (  90 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_47,axiom,(
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

tff(f_101,axiom,(
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

tff(f_57,axiom,(
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

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2629,plain,(
    ! [C_232,A_233,B_234] :
      ( v2_funct_1(C_232)
      | ~ v3_funct_2(C_232,A_233,B_234)
      | ~ v1_funct_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2635,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2629])).

tff(c_2643,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2635])).

tff(c_44,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_20,plain,(
    ! [A_19] : m1_subset_1(k6_relat_1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    ! [A_19] : m1_subset_1(k6_partfun1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_2699,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( r2_relset_1(A_244,B_245,C_246,C_246)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2709,plain,(
    ! [A_248,C_249] :
      ( r2_relset_1(A_248,A_248,C_249,C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,A_248))) ) ),
    inference(resolution,[status(thm)],[c_57,c_2699])).

tff(c_2717,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_57,c_2709])).

tff(c_2447,plain,(
    ! [C_200,B_201,A_202] :
      ( v5_relat_1(C_200,B_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2459,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2447])).

tff(c_2464,plain,(
    ! [B_207,A_208] :
      ( k2_relat_1(B_207) = A_208
      | ~ v2_funct_2(B_207,A_208)
      | ~ v5_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2473,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2459,c_2464])).

tff(c_2480,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2473])).

tff(c_2481,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2480])).

tff(c_2554,plain,(
    ! [C_222,B_223,A_224] :
      ( v2_funct_2(C_222,B_223)
      | ~ v3_funct_2(C_222,A_224,B_223)
      | ~ v1_funct_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2560,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2554])).

tff(c_2568,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2560])).

tff(c_2570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2481,c_2568])).

tff(c_2571,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2480])).

tff(c_8,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_partfun1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2752,plain,(
    ! [A_259,B_260] :
      ( k2_funct_2(A_259,B_260) = k2_funct_1(B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2758,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2752])).

tff(c_2766,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2758])).

tff(c_2734,plain,(
    ! [A_254,B_255] :
      ( v1_funct_1(k2_funct_2(A_254,B_255))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_zfmisc_1(A_254,A_254)))
      | ~ v3_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2740,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2734])).

tff(c_2748,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2740])).

tff(c_2768,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_2748])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_funct_2(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_25,A_25)))
      | ~ v3_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_2(B_26,A_25,A_25)
      | ~ v1_funct_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2942,plain,(
    ! [B_279,E_278,A_280,F_275,D_277,C_276] :
      ( k1_partfun1(A_280,B_279,C_276,D_277,E_278,F_275) = k5_relat_1(E_278,F_275)
      | ~ m1_subset_1(F_275,k1_zfmisc_1(k2_zfmisc_1(C_276,D_277)))
      | ~ v1_funct_1(F_275)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279)))
      | ~ v1_funct_1(E_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2950,plain,(
    ! [A_280,B_279,E_278] :
      ( k1_partfun1(A_280,B_279,'#skF_2','#skF_2',E_278,'#skF_3') = k5_relat_1(E_278,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279)))
      | ~ v1_funct_1(E_278) ) ),
    inference(resolution,[status(thm)],[c_50,c_2942])).

tff(c_2964,plain,(
    ! [A_281,B_282,E_283] :
      ( k1_partfun1(A_281,B_282,'#skF_2','#skF_2',E_283,'#skF_3') = k5_relat_1(E_283,'#skF_3')
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(E_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2950])).

tff(c_3329,plain,(
    ! [A_294,B_295] :
      ( k1_partfun1(A_294,A_294,'#skF_2','#skF_2',k2_funct_2(A_294,B_295),'#skF_3') = k5_relat_1(k2_funct_2(A_294,B_295),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_294,B_295))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(k2_zfmisc_1(A_294,A_294)))
      | ~ v3_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_1(B_295) ) ),
    inference(resolution,[status(thm)],[c_32,c_2964])).

tff(c_3341,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3329])).

tff(c_3358,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2768,c_2766,c_2766,c_2766,c_3341])).

tff(c_282,plain,(
    ! [C_83,A_84,B_85] :
      ( v2_funct_1(C_83)
      | ~ v3_funct_2(C_83,A_84,B_85)
      | ~ v1_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_288,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_282])).

tff(c_296,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_288])).

tff(c_325,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_relset_1(A_93,B_94,C_95,C_95)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_335,plain,(
    ! [A_97,C_98] :
      ( r2_relset_1(A_97,A_97,C_98,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97))) ) ),
    inference(resolution,[status(thm)],[c_57,c_325])).

tff(c_343,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_57,c_335])).

tff(c_236,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_248,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_236])).

tff(c_347,plain,(
    ! [A_100,B_101] :
      ( k1_relset_1(A_100,A_100,B_101) = A_100
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100)))
      | ~ v1_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_353,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_347])).

tff(c_362,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_248,c_353])).

tff(c_10,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_406,plain,(
    ! [A_110,B_111] :
      ( k2_funct_2(A_110,B_111) = k2_funct_1(B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v3_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_412,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_406])).

tff(c_420,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_412])).

tff(c_390,plain,(
    ! [A_108,B_109] :
      ( v1_funct_1(k2_funct_2(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_396,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_390])).

tff(c_404,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_396])).

tff(c_422,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_404])).

tff(c_574,plain,(
    ! [A_131,E_129,B_130,F_126,C_127,D_128] :
      ( k1_partfun1(A_131,B_130,C_127,D_128,E_129,F_126) = k5_relat_1(E_129,F_126)
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_127,D_128)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130)))
      | ~ v1_funct_1(E_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2278,plain,(
    ! [E_188,A_185,B_189,A_187,B_186] :
      ( k1_partfun1(A_185,B_186,A_187,A_187,E_188,k2_funct_2(A_187,B_189)) = k5_relat_1(E_188,k2_funct_2(A_187,B_189))
      | ~ v1_funct_1(k2_funct_2(A_187,B_189))
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_1(E_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_189,A_187,A_187)
      | ~ v1_funct_2(B_189,A_187,A_187)
      | ~ v1_funct_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_32,c_574])).

tff(c_2300,plain,(
    ! [A_187,B_189] :
      ( k1_partfun1('#skF_2','#skF_2',A_187,A_187,'#skF_3',k2_funct_2(A_187,B_189)) = k5_relat_1('#skF_3',k2_funct_2(A_187,B_189))
      | ~ v1_funct_1(k2_funct_2(A_187,B_189))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_189,A_187,A_187)
      | ~ v1_funct_2(B_189,A_187,A_187)
      | ~ v1_funct_1(B_189) ) ),
    inference(resolution,[status(thm)],[c_50,c_2278])).

tff(c_2360,plain,(
    ! [A_190,B_191] :
      ( k1_partfun1('#skF_2','#skF_2',A_190,A_190,'#skF_3',k2_funct_2(A_190,B_191)) = k5_relat_1('#skF_3',k2_funct_2(A_190,B_191))
      | ~ v1_funct_1(k2_funct_2(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2300])).

tff(c_2382,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2360])).

tff(c_2414,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_422,c_420,c_420,c_420,c_2382])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_90,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_423,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_90])).

tff(c_2416,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2414,c_423])).

tff(c_2423,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2416])).

tff(c_2426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_56,c_296,c_343,c_362,c_2423])).

tff(c_2427,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2770,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_2427])).

tff(c_3387,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3358,c_2770])).

tff(c_3394,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_3387])).

tff(c_3397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_56,c_2643,c_2717,c_2571,c_3394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.26  
% 5.96/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.27  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.96/2.27  
% 5.96/2.27  %Foreground sorts:
% 5.96/2.27  
% 5.96/2.27  
% 5.96/2.27  %Background operators:
% 5.96/2.27  
% 5.96/2.27  
% 5.96/2.27  %Foreground operators:
% 5.96/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.96/2.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.96/2.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.96/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.96/2.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.96/2.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.96/2.27  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.96/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.96/2.27  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.96/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.96/2.27  tff('#skF_2', type, '#skF_2': $i).
% 5.96/2.27  tff('#skF_3', type, '#skF_3': $i).
% 5.96/2.27  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.96/2.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.96/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.96/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.96/2.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.96/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.96/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.96/2.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.96/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.96/2.27  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.96/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.96/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.96/2.27  
% 5.96/2.29  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.96/2.29  tff(f_144, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.96/2.29  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.96/2.29  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.96/2.29  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.96/2.29  tff(f_65, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.96/2.29  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.96/2.29  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.96/2.29  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.96/2.29  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.96/2.29  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.96/2.29  tff(f_101, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.96/2.29  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.96/2.29  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.96/2.29  tff(f_131, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.96/2.29  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.96/2.29  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.96/2.29  tff(c_72, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.96/2.29  tff(c_78, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_72])).
% 5.96/2.29  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_78])).
% 5.96/2.29  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.96/2.29  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.96/2.29  tff(c_2629, plain, (![C_232, A_233, B_234]: (v2_funct_1(C_232) | ~v3_funct_2(C_232, A_233, B_234) | ~v1_funct_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.96/2.29  tff(c_2635, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2629])).
% 5.96/2.29  tff(c_2643, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2635])).
% 5.96/2.29  tff(c_44, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.96/2.29  tff(c_20, plain, (![A_19]: (m1_subset_1(k6_relat_1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.96/2.29  tff(c_57, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 5.96/2.29  tff(c_2699, plain, (![A_244, B_245, C_246, D_247]: (r2_relset_1(A_244, B_245, C_246, C_246) | ~m1_subset_1(D_247, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.96/2.29  tff(c_2709, plain, (![A_248, C_249]: (r2_relset_1(A_248, A_248, C_249, C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, A_248))))), inference(resolution, [status(thm)], [c_57, c_2699])).
% 5.96/2.29  tff(c_2717, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_57, c_2709])).
% 5.96/2.29  tff(c_2447, plain, (![C_200, B_201, A_202]: (v5_relat_1(C_200, B_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.96/2.29  tff(c_2459, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_2447])).
% 5.96/2.29  tff(c_2464, plain, (![B_207, A_208]: (k2_relat_1(B_207)=A_208 | ~v2_funct_2(B_207, A_208) | ~v5_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.96/2.29  tff(c_2473, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2459, c_2464])).
% 5.96/2.29  tff(c_2480, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2473])).
% 5.96/2.29  tff(c_2481, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2480])).
% 5.96/2.29  tff(c_2554, plain, (![C_222, B_223, A_224]: (v2_funct_2(C_222, B_223) | ~v3_funct_2(C_222, A_224, B_223) | ~v1_funct_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.96/2.29  tff(c_2560, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2554])).
% 5.96/2.29  tff(c_2568, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2560])).
% 5.96/2.29  tff(c_2570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2481, c_2568])).
% 5.96/2.29  tff(c_2571, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2480])).
% 5.96/2.29  tff(c_8, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.96/2.29  tff(c_59, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_partfun1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 5.96/2.29  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.96/2.29  tff(c_2752, plain, (![A_259, B_260]: (k2_funct_2(A_259, B_260)=k2_funct_1(B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.96/2.29  tff(c_2758, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2752])).
% 5.96/2.29  tff(c_2766, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2758])).
% 5.96/2.29  tff(c_2734, plain, (![A_254, B_255]: (v1_funct_1(k2_funct_2(A_254, B_255)) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_zfmisc_1(A_254, A_254))) | ~v3_funct_2(B_255, A_254, A_254) | ~v1_funct_2(B_255, A_254, A_254) | ~v1_funct_1(B_255))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.96/2.29  tff(c_2740, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2734])).
% 5.96/2.29  tff(c_2748, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2740])).
% 5.96/2.29  tff(c_2768, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_2748])).
% 5.96/2.29  tff(c_32, plain, (![A_25, B_26]: (m1_subset_1(k2_funct_2(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_25, A_25))) | ~v3_funct_2(B_26, A_25, A_25) | ~v1_funct_2(B_26, A_25, A_25) | ~v1_funct_1(B_26))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.96/2.29  tff(c_2942, plain, (![B_279, E_278, A_280, F_275, D_277, C_276]: (k1_partfun1(A_280, B_279, C_276, D_277, E_278, F_275)=k5_relat_1(E_278, F_275) | ~m1_subset_1(F_275, k1_zfmisc_1(k2_zfmisc_1(C_276, D_277))) | ~v1_funct_1(F_275) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))) | ~v1_funct_1(E_278))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.96/2.29  tff(c_2950, plain, (![A_280, B_279, E_278]: (k1_partfun1(A_280, B_279, '#skF_2', '#skF_2', E_278, '#skF_3')=k5_relat_1(E_278, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))) | ~v1_funct_1(E_278))), inference(resolution, [status(thm)], [c_50, c_2942])).
% 5.96/2.29  tff(c_2964, plain, (![A_281, B_282, E_283]: (k1_partfun1(A_281, B_282, '#skF_2', '#skF_2', E_283, '#skF_3')=k5_relat_1(E_283, '#skF_3') | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(E_283))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2950])).
% 5.96/2.29  tff(c_3329, plain, (![A_294, B_295]: (k1_partfun1(A_294, A_294, '#skF_2', '#skF_2', k2_funct_2(A_294, B_295), '#skF_3')=k5_relat_1(k2_funct_2(A_294, B_295), '#skF_3') | ~v1_funct_1(k2_funct_2(A_294, B_295)) | ~m1_subset_1(B_295, k1_zfmisc_1(k2_zfmisc_1(A_294, A_294))) | ~v3_funct_2(B_295, A_294, A_294) | ~v1_funct_2(B_295, A_294, A_294) | ~v1_funct_1(B_295))), inference(resolution, [status(thm)], [c_32, c_2964])).
% 5.96/2.29  tff(c_3341, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3329])).
% 5.96/2.29  tff(c_3358, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2768, c_2766, c_2766, c_2766, c_3341])).
% 5.96/2.29  tff(c_282, plain, (![C_83, A_84, B_85]: (v2_funct_1(C_83) | ~v3_funct_2(C_83, A_84, B_85) | ~v1_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.96/2.29  tff(c_288, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_282])).
% 5.96/2.29  tff(c_296, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_288])).
% 5.96/2.29  tff(c_325, plain, (![A_93, B_94, C_95, D_96]: (r2_relset_1(A_93, B_94, C_95, C_95) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.96/2.29  tff(c_335, plain, (![A_97, C_98]: (r2_relset_1(A_97, A_97, C_98, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))))), inference(resolution, [status(thm)], [c_57, c_325])).
% 5.96/2.29  tff(c_343, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_57, c_335])).
% 5.96/2.29  tff(c_236, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.96/2.29  tff(c_248, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_236])).
% 5.96/2.29  tff(c_347, plain, (![A_100, B_101]: (k1_relset_1(A_100, A_100, B_101)=A_100 | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))) | ~v1_funct_2(B_101, A_100, A_100) | ~v1_funct_1(B_101))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.96/2.29  tff(c_353, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_347])).
% 5.96/2.29  tff(c_362, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_248, c_353])).
% 5.96/2.29  tff(c_10, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.96/2.29  tff(c_58, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 5.96/2.29  tff(c_406, plain, (![A_110, B_111]: (k2_funct_2(A_110, B_111)=k2_funct_1(B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v3_funct_2(B_111, A_110, A_110) | ~v1_funct_2(B_111, A_110, A_110) | ~v1_funct_1(B_111))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.96/2.29  tff(c_412, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_406])).
% 5.96/2.29  tff(c_420, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_412])).
% 5.96/2.29  tff(c_390, plain, (![A_108, B_109]: (v1_funct_1(k2_funct_2(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.96/2.29  tff(c_396, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_390])).
% 5.96/2.29  tff(c_404, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_396])).
% 5.96/2.29  tff(c_422, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_404])).
% 5.96/2.29  tff(c_574, plain, (![A_131, E_129, B_130, F_126, C_127, D_128]: (k1_partfun1(A_131, B_130, C_127, D_128, E_129, F_126)=k5_relat_1(E_129, F_126) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_127, D_128))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))) | ~v1_funct_1(E_129))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.96/2.29  tff(c_2278, plain, (![E_188, A_185, B_189, A_187, B_186]: (k1_partfun1(A_185, B_186, A_187, A_187, E_188, k2_funct_2(A_187, B_189))=k5_relat_1(E_188, k2_funct_2(A_187, B_189)) | ~v1_funct_1(k2_funct_2(A_187, B_189)) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_1(E_188) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_189, A_187, A_187) | ~v1_funct_2(B_189, A_187, A_187) | ~v1_funct_1(B_189))), inference(resolution, [status(thm)], [c_32, c_574])).
% 5.96/2.29  tff(c_2300, plain, (![A_187, B_189]: (k1_partfun1('#skF_2', '#skF_2', A_187, A_187, '#skF_3', k2_funct_2(A_187, B_189))=k5_relat_1('#skF_3', k2_funct_2(A_187, B_189)) | ~v1_funct_1(k2_funct_2(A_187, B_189)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_189, A_187, A_187) | ~v1_funct_2(B_189, A_187, A_187) | ~v1_funct_1(B_189))), inference(resolution, [status(thm)], [c_50, c_2278])).
% 5.96/2.29  tff(c_2360, plain, (![A_190, B_191]: (k1_partfun1('#skF_2', '#skF_2', A_190, A_190, '#skF_3', k2_funct_2(A_190, B_191))=k5_relat_1('#skF_3', k2_funct_2(A_190, B_191)) | ~v1_funct_1(k2_funct_2(A_190, B_191)) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2300])).
% 5.96/2.29  tff(c_2382, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2360])).
% 5.96/2.29  tff(c_2414, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_422, c_420, c_420, c_420, c_2382])).
% 5.96/2.29  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.96/2.29  tff(c_90, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.96/2.29  tff(c_423, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_90])).
% 5.96/2.29  tff(c_2416, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2414, c_423])).
% 5.96/2.29  tff(c_2423, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2416])).
% 5.96/2.29  tff(c_2426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_56, c_296, c_343, c_362, c_2423])).
% 5.96/2.29  tff(c_2427, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 5.96/2.29  tff(c_2770, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_2427])).
% 5.96/2.29  tff(c_3387, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3358, c_2770])).
% 5.96/2.29  tff(c_3394, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59, c_3387])).
% 5.96/2.29  tff(c_3397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_56, c_2643, c_2717, c_2571, c_3394])).
% 5.96/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.29  
% 5.96/2.29  Inference rules
% 5.96/2.29  ----------------------
% 5.96/2.29  #Ref     : 0
% 5.96/2.29  #Sup     : 714
% 5.96/2.29  #Fact    : 0
% 5.96/2.29  #Define  : 0
% 5.96/2.29  #Split   : 3
% 5.96/2.29  #Chain   : 0
% 5.96/2.29  #Close   : 0
% 5.96/2.29  
% 5.96/2.29  Ordering : KBO
% 5.96/2.29  
% 5.96/2.29  Simplification rules
% 5.96/2.29  ----------------------
% 5.96/2.29  #Subsume      : 6
% 5.96/2.29  #Demod        : 1645
% 5.96/2.29  #Tautology    : 284
% 5.96/2.29  #SimpNegUnit  : 2
% 5.96/2.29  #BackRed      : 67
% 5.96/2.29  
% 5.96/2.29  #Partial instantiations: 0
% 5.96/2.29  #Strategies tried      : 1
% 5.96/2.29  
% 5.96/2.29  Timing (in seconds)
% 5.96/2.29  ----------------------
% 5.96/2.29  Preprocessing        : 0.37
% 5.96/2.29  Parsing              : 0.20
% 5.96/2.29  CNF conversion       : 0.02
% 5.96/2.29  Main loop            : 1.08
% 5.96/2.30  Inferencing          : 0.35
% 5.96/2.30  Reduction            : 0.43
% 5.96/2.30  Demodulation         : 0.33
% 5.96/2.30  BG Simplification    : 0.03
% 5.96/2.30  Subsumption          : 0.19
% 5.96/2.30  Abstraction          : 0.04
% 5.96/2.30  MUC search           : 0.00
% 5.96/2.30  Cooper               : 0.00
% 5.96/2.30  Total                : 1.50
% 5.96/2.30  Index Insertion      : 0.00
% 5.96/2.30  Index Deletion       : 0.00
% 5.96/2.30  Index Matching       : 0.00
% 5.96/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
