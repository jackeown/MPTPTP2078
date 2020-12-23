%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:05 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 357 expanded)
%              Number of leaves         :   41 ( 153 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 (1067 expanded)
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

tff(f_139,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_118,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_96,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2392,plain,(
    ! [C_226,A_227,B_228] :
      ( v2_funct_1(C_226)
      | ~ v3_funct_2(C_226,A_227,B_228)
      | ~ v1_funct_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2398,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2392])).

tff(c_2406,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2398])).

tff(c_42,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_18,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_2463,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( r2_relset_1(A_241,B_242,C_243,C_243)
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2473,plain,(
    ! [A_245,C_246] :
      ( r2_relset_1(A_245,A_245,C_246,C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_245,A_245))) ) ),
    inference(resolution,[status(thm)],[c_55,c_2463])).

tff(c_2481,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_55,c_2473])).

tff(c_2220,plain,(
    ! [C_194,B_195,A_196] :
      ( v5_relat_1(C_194,B_195)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2232,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2220])).

tff(c_2253,plain,(
    ! [B_207,A_208] :
      ( k2_relat_1(B_207) = A_208
      | ~ v2_funct_2(B_207,A_208)
      | ~ v5_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2262,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2232,c_2253])).

tff(c_2271,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2262])).

tff(c_2290,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2271])).

tff(c_2335,plain,(
    ! [C_219,B_220,A_221] :
      ( v2_funct_2(C_219,B_220)
      | ~ v3_funct_2(C_219,A_221,B_220)
      | ~ v1_funct_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2341,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2335])).

tff(c_2349,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_2341])).

tff(c_2351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2290,c_2349])).

tff(c_2352,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2271])).

tff(c_4,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2517,plain,(
    ! [A_256,B_257] :
      ( k2_funct_2(A_256,B_257) = k2_funct_1(B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_zfmisc_1(A_256,A_256)))
      | ~ v3_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_2(B_257,A_256,A_256)
      | ~ v1_funct_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2523,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2517])).

tff(c_2531,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2523])).

tff(c_2501,plain,(
    ! [A_254,B_255] :
      ( v1_funct_1(k2_funct_2(A_254,B_255))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_zfmisc_1(A_254,A_254)))
      | ~ v3_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2507,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2501])).

tff(c_2515,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2507])).

tff(c_2533,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_2515])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_funct_2(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2687,plain,(
    ! [C_273,A_272,B_275,F_274,D_271,E_276] :
      ( k1_partfun1(A_272,B_275,C_273,D_271,E_276,F_274) = k5_relat_1(E_276,F_274)
      | ~ m1_subset_1(F_274,k1_zfmisc_1(k2_zfmisc_1(C_273,D_271)))
      | ~ v1_funct_1(F_274)
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(A_272,B_275)))
      | ~ v1_funct_1(E_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2695,plain,(
    ! [A_272,B_275,E_276] :
      ( k1_partfun1(A_272,B_275,'#skF_2','#skF_2',E_276,'#skF_3') = k5_relat_1(E_276,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(A_272,B_275)))
      | ~ v1_funct_1(E_276) ) ),
    inference(resolution,[status(thm)],[c_48,c_2687])).

tff(c_2712,plain,(
    ! [A_277,B_278,E_279] :
      ( k1_partfun1(A_277,B_278,'#skF_2','#skF_2',E_279,'#skF_3') = k5_relat_1(E_279,'#skF_3')
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ v1_funct_1(E_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2695])).

tff(c_3070,plain,(
    ! [A_290,B_291] :
      ( k1_partfun1(A_290,A_290,'#skF_2','#skF_2',k2_funct_2(A_290,B_291),'#skF_3') = k5_relat_1(k2_funct_2(A_290,B_291),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_290,B_291))
      | ~ m1_subset_1(B_291,k1_zfmisc_1(k2_zfmisc_1(A_290,A_290)))
      | ~ v3_funct_2(B_291,A_290,A_290)
      | ~ v1_funct_2(B_291,A_290,A_290)
      | ~ v1_funct_1(B_291) ) ),
    inference(resolution,[status(thm)],[c_30,c_2712])).

tff(c_3082,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_3070])).

tff(c_3099,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_2533,c_2531,c_2531,c_2531,c_3082])).

tff(c_286,plain,(
    ! [C_83,A_84,B_85] :
      ( v2_funct_1(C_83)
      | ~ v3_funct_2(C_83,A_84,B_85)
      | ~ v1_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_292,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_286])).

tff(c_300,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_292])).

tff(c_357,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( r2_relset_1(A_97,B_98,C_99,C_99)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_367,plain,(
    ! [A_101,C_102] :
      ( r2_relset_1(A_101,A_101,C_102,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,A_101))) ) ),
    inference(resolution,[status(thm)],[c_55,c_357])).

tff(c_375,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_55,c_367])).

tff(c_240,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_252,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_240])).

tff(c_330,plain,(
    ! [A_95,B_96] :
      ( k1_relset_1(A_95,A_95,B_96) = A_95
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_336,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_330])).

tff(c_345,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_252,c_336])).

tff(c_6,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_412,plain,(
    ! [A_113,B_114] :
      ( k2_funct_2(A_113,B_114) = k2_funct_1(B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(A_113,A_113)))
      | ~ v3_funct_2(B_114,A_113,A_113)
      | ~ v1_funct_2(B_114,A_113,A_113)
      | ~ v1_funct_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_418,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_412])).

tff(c_426,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_418])).

tff(c_396,plain,(
    ! [A_111,B_112] :
      ( v1_funct_1(k2_funct_2(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_111,A_111)))
      | ~ v3_funct_2(B_112,A_111,A_111)
      | ~ v1_funct_2(B_112,A_111,A_111)
      | ~ v1_funct_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_402,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_396])).

tff(c_410,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_402])).

tff(c_428,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_410])).

tff(c_577,plain,(
    ! [D_130,C_132,A_131,E_135,F_133,B_134] :
      ( k1_partfun1(A_131,B_134,C_132,D_130,E_135,F_133) = k5_relat_1(E_135,F_133)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_132,D_130)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_131,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2101,plain,(
    ! [B_185,A_187,E_186,A_183,B_184] :
      ( k1_partfun1(A_183,B_184,A_187,A_187,E_186,k2_funct_2(A_187,B_185)) = k5_relat_1(E_186,k2_funct_2(A_187,B_185))
      | ~ v1_funct_1(k2_funct_2(A_187,B_185))
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_185,A_187,A_187)
      | ~ v1_funct_2(B_185,A_187,A_187)
      | ~ v1_funct_1(B_185) ) ),
    inference(resolution,[status(thm)],[c_30,c_577])).

tff(c_2121,plain,(
    ! [A_187,B_185] :
      ( k1_partfun1('#skF_2','#skF_2',A_187,A_187,'#skF_3',k2_funct_2(A_187,B_185)) = k5_relat_1('#skF_3',k2_funct_2(A_187,B_185))
      | ~ v1_funct_1(k2_funct_2(A_187,B_185))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_zfmisc_1(A_187,A_187)))
      | ~ v3_funct_2(B_185,A_187,A_187)
      | ~ v1_funct_2(B_185,A_187,A_187)
      | ~ v1_funct_1(B_185) ) ),
    inference(resolution,[status(thm)],[c_48,c_2101])).

tff(c_2154,plain,(
    ! [A_189,B_190] :
      ( k1_partfun1('#skF_2','#skF_2',A_189,A_189,'#skF_3',k2_funct_2(A_189,B_190)) = k5_relat_1('#skF_3',k2_funct_2(A_189,B_190))
      | ~ v1_funct_1(k2_funct_2(A_189,B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2121])).

tff(c_2174,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2154])).

tff(c_2203,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_428,c_426,c_426,c_426,c_2174])).

tff(c_46,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_83,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_429,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_83])).

tff(c_2205,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2203,c_429])).

tff(c_2212,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2205])).

tff(c_2215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_300,c_375,c_345,c_2212])).

tff(c_2216,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2534,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2531,c_2216])).

tff(c_3113,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3099,c_2534])).

tff(c_3120,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_3113])).

tff(c_3123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_2406,c_2481,c_2352,c_3120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.14  
% 5.91/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.15  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 5.91/2.15  
% 5.91/2.15  %Foreground sorts:
% 5.91/2.15  
% 5.91/2.15  
% 5.91/2.15  %Background operators:
% 5.91/2.15  
% 5.91/2.15  
% 5.91/2.15  %Foreground operators:
% 5.91/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.91/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.91/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.91/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.91/2.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.91/2.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.91/2.15  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.91/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.91/2.15  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.91/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.91/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.91/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.15  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.91/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.91/2.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.91/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.91/2.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.91/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.91/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.91/2.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.91/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.91/2.15  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.91/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.91/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.91/2.15  
% 5.91/2.17  tff(f_139, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.91/2.17  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.91/2.17  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.91/2.17  tff(f_118, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.91/2.17  tff(f_60, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.91/2.17  tff(f_58, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.91/2.17  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.91/2.17  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.91/2.17  tff(f_38, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.91/2.17  tff(f_116, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.91/2.17  tff(f_96, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.91/2.17  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.91/2.17  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.91/2.17  tff(f_126, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.91/2.17  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.91/2.17  tff(c_69, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.91/2.17  tff(c_81, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_69])).
% 5.91/2.17  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.91/2.17  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.91/2.17  tff(c_2392, plain, (![C_226, A_227, B_228]: (v2_funct_1(C_226) | ~v3_funct_2(C_226, A_227, B_228) | ~v1_funct_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.91/2.17  tff(c_2398, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2392])).
% 5.91/2.17  tff(c_2406, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2398])).
% 5.91/2.17  tff(c_42, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.91/2.17  tff(c_18, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.91/2.17  tff(c_55, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 5.91/2.17  tff(c_2463, plain, (![A_241, B_242, C_243, D_244]: (r2_relset_1(A_241, B_242, C_243, C_243) | ~m1_subset_1(D_244, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.91/2.17  tff(c_2473, plain, (![A_245, C_246]: (r2_relset_1(A_245, A_245, C_246, C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_245, A_245))))), inference(resolution, [status(thm)], [c_55, c_2463])).
% 5.91/2.17  tff(c_2481, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_55, c_2473])).
% 5.91/2.17  tff(c_2220, plain, (![C_194, B_195, A_196]: (v5_relat_1(C_194, B_195) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.91/2.17  tff(c_2232, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_2220])).
% 5.91/2.17  tff(c_2253, plain, (![B_207, A_208]: (k2_relat_1(B_207)=A_208 | ~v2_funct_2(B_207, A_208) | ~v5_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.91/2.17  tff(c_2262, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2232, c_2253])).
% 5.91/2.17  tff(c_2271, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2262])).
% 5.91/2.17  tff(c_2290, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2271])).
% 5.91/2.17  tff(c_2335, plain, (![C_219, B_220, A_221]: (v2_funct_2(C_219, B_220) | ~v3_funct_2(C_219, A_221, B_220) | ~v1_funct_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.91/2.17  tff(c_2341, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2335])).
% 5.91/2.17  tff(c_2349, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_2341])).
% 5.91/2.17  tff(c_2351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2290, c_2349])).
% 5.91/2.17  tff(c_2352, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2271])).
% 5.91/2.17  tff(c_4, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.91/2.17  tff(c_57, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 5.91/2.17  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.91/2.17  tff(c_2517, plain, (![A_256, B_257]: (k2_funct_2(A_256, B_257)=k2_funct_1(B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(k2_zfmisc_1(A_256, A_256))) | ~v3_funct_2(B_257, A_256, A_256) | ~v1_funct_2(B_257, A_256, A_256) | ~v1_funct_1(B_257))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.91/2.17  tff(c_2523, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2517])).
% 5.91/2.17  tff(c_2531, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2523])).
% 5.91/2.17  tff(c_2501, plain, (![A_254, B_255]: (v1_funct_1(k2_funct_2(A_254, B_255)) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_zfmisc_1(A_254, A_254))) | ~v3_funct_2(B_255, A_254, A_254) | ~v1_funct_2(B_255, A_254, A_254) | ~v1_funct_1(B_255))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.91/2.17  tff(c_2507, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2501])).
% 5.91/2.17  tff(c_2515, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2507])).
% 5.91/2.17  tff(c_2533, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_2515])).
% 5.91/2.17  tff(c_30, plain, (![A_23, B_24]: (m1_subset_1(k2_funct_2(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.91/2.17  tff(c_2687, plain, (![C_273, A_272, B_275, F_274, D_271, E_276]: (k1_partfun1(A_272, B_275, C_273, D_271, E_276, F_274)=k5_relat_1(E_276, F_274) | ~m1_subset_1(F_274, k1_zfmisc_1(k2_zfmisc_1(C_273, D_271))) | ~v1_funct_1(F_274) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(A_272, B_275))) | ~v1_funct_1(E_276))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.17  tff(c_2695, plain, (![A_272, B_275, E_276]: (k1_partfun1(A_272, B_275, '#skF_2', '#skF_2', E_276, '#skF_3')=k5_relat_1(E_276, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(A_272, B_275))) | ~v1_funct_1(E_276))), inference(resolution, [status(thm)], [c_48, c_2687])).
% 5.91/2.17  tff(c_2712, plain, (![A_277, B_278, E_279]: (k1_partfun1(A_277, B_278, '#skF_2', '#skF_2', E_279, '#skF_3')=k5_relat_1(E_279, '#skF_3') | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~v1_funct_1(E_279))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2695])).
% 5.91/2.17  tff(c_3070, plain, (![A_290, B_291]: (k1_partfun1(A_290, A_290, '#skF_2', '#skF_2', k2_funct_2(A_290, B_291), '#skF_3')=k5_relat_1(k2_funct_2(A_290, B_291), '#skF_3') | ~v1_funct_1(k2_funct_2(A_290, B_291)) | ~m1_subset_1(B_291, k1_zfmisc_1(k2_zfmisc_1(A_290, A_290))) | ~v3_funct_2(B_291, A_290, A_290) | ~v1_funct_2(B_291, A_290, A_290) | ~v1_funct_1(B_291))), inference(resolution, [status(thm)], [c_30, c_2712])).
% 5.91/2.17  tff(c_3082, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_3070])).
% 5.91/2.17  tff(c_3099, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_2533, c_2531, c_2531, c_2531, c_3082])).
% 5.91/2.17  tff(c_286, plain, (![C_83, A_84, B_85]: (v2_funct_1(C_83) | ~v3_funct_2(C_83, A_84, B_85) | ~v1_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.91/2.17  tff(c_292, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_286])).
% 5.91/2.17  tff(c_300, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_292])).
% 5.91/2.17  tff(c_357, plain, (![A_97, B_98, C_99, D_100]: (r2_relset_1(A_97, B_98, C_99, C_99) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.91/2.17  tff(c_367, plain, (![A_101, C_102]: (r2_relset_1(A_101, A_101, C_102, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, A_101))))), inference(resolution, [status(thm)], [c_55, c_357])).
% 5.91/2.17  tff(c_375, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_55, c_367])).
% 5.91/2.17  tff(c_240, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.91/2.17  tff(c_252, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_240])).
% 5.91/2.17  tff(c_330, plain, (![A_95, B_96]: (k1_relset_1(A_95, A_95, B_96)=A_95 | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.91/2.17  tff(c_336, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_330])).
% 5.91/2.17  tff(c_345, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_252, c_336])).
% 5.91/2.17  tff(c_6, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.91/2.17  tff(c_56, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 5.91/2.17  tff(c_412, plain, (![A_113, B_114]: (k2_funct_2(A_113, B_114)=k2_funct_1(B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(k2_zfmisc_1(A_113, A_113))) | ~v3_funct_2(B_114, A_113, A_113) | ~v1_funct_2(B_114, A_113, A_113) | ~v1_funct_1(B_114))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.91/2.17  tff(c_418, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_412])).
% 5.91/2.17  tff(c_426, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_418])).
% 5.91/2.17  tff(c_396, plain, (![A_111, B_112]: (v1_funct_1(k2_funct_2(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(A_111, A_111))) | ~v3_funct_2(B_112, A_111, A_111) | ~v1_funct_2(B_112, A_111, A_111) | ~v1_funct_1(B_112))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.91/2.17  tff(c_402, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_396])).
% 5.91/2.17  tff(c_410, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_402])).
% 5.91/2.17  tff(c_428, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_410])).
% 5.91/2.17  tff(c_577, plain, (![D_130, C_132, A_131, E_135, F_133, B_134]: (k1_partfun1(A_131, B_134, C_132, D_130, E_135, F_133)=k5_relat_1(E_135, F_133) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_132, D_130))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_131, B_134))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.17  tff(c_2101, plain, (![B_185, A_187, E_186, A_183, B_184]: (k1_partfun1(A_183, B_184, A_187, A_187, E_186, k2_funct_2(A_187, B_185))=k5_relat_1(E_186, k2_funct_2(A_187, B_185)) | ~v1_funct_1(k2_funct_2(A_187, B_185)) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(E_186) | ~m1_subset_1(B_185, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_185, A_187, A_187) | ~v1_funct_2(B_185, A_187, A_187) | ~v1_funct_1(B_185))), inference(resolution, [status(thm)], [c_30, c_577])).
% 5.91/2.17  tff(c_2121, plain, (![A_187, B_185]: (k1_partfun1('#skF_2', '#skF_2', A_187, A_187, '#skF_3', k2_funct_2(A_187, B_185))=k5_relat_1('#skF_3', k2_funct_2(A_187, B_185)) | ~v1_funct_1(k2_funct_2(A_187, B_185)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_185, k1_zfmisc_1(k2_zfmisc_1(A_187, A_187))) | ~v3_funct_2(B_185, A_187, A_187) | ~v1_funct_2(B_185, A_187, A_187) | ~v1_funct_1(B_185))), inference(resolution, [status(thm)], [c_48, c_2101])).
% 5.91/2.17  tff(c_2154, plain, (![A_189, B_190]: (k1_partfun1('#skF_2', '#skF_2', A_189, A_189, '#skF_3', k2_funct_2(A_189, B_190))=k5_relat_1('#skF_3', k2_funct_2(A_189, B_190)) | ~v1_funct_1(k2_funct_2(A_189, B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2121])).
% 5.91/2.17  tff(c_2174, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2154])).
% 5.91/2.17  tff(c_2203, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_428, c_426, c_426, c_426, c_2174])).
% 5.91/2.17  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.91/2.17  tff(c_83, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.91/2.17  tff(c_429, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_83])).
% 5.91/2.17  tff(c_2205, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2203, c_429])).
% 5.91/2.17  tff(c_2212, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_56, c_2205])).
% 5.91/2.17  tff(c_2215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_300, c_375, c_345, c_2212])).
% 5.91/2.17  tff(c_2216, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 5.91/2.17  tff(c_2534, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2531, c_2216])).
% 5.91/2.17  tff(c_3113, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3099, c_2534])).
% 5.91/2.17  tff(c_3120, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_57, c_3113])).
% 5.91/2.17  tff(c_3123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_2406, c_2481, c_2352, c_3120])).
% 5.91/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.17  
% 5.91/2.17  Inference rules
% 5.91/2.17  ----------------------
% 5.91/2.17  #Ref     : 0
% 5.91/2.17  #Sup     : 658
% 5.91/2.17  #Fact    : 0
% 5.91/2.17  #Define  : 0
% 5.91/2.17  #Split   : 3
% 5.91/2.17  #Chain   : 0
% 5.91/2.17  #Close   : 0
% 5.91/2.17  
% 5.91/2.17  Ordering : KBO
% 5.91/2.17  
% 5.91/2.17  Simplification rules
% 5.91/2.17  ----------------------
% 5.91/2.17  #Subsume      : 6
% 5.91/2.17  #Demod        : 1469
% 5.91/2.17  #Tautology    : 254
% 5.91/2.17  #SimpNegUnit  : 2
% 5.91/2.17  #BackRed      : 57
% 5.91/2.17  
% 5.91/2.17  #Partial instantiations: 0
% 5.91/2.17  #Strategies tried      : 1
% 5.91/2.17  
% 5.91/2.17  Timing (in seconds)
% 5.91/2.17  ----------------------
% 6.14/2.17  Preprocessing        : 0.35
% 6.14/2.17  Parsing              : 0.19
% 6.14/2.17  CNF conversion       : 0.02
% 6.14/2.17  Main loop            : 1.01
% 6.14/2.17  Inferencing          : 0.33
% 6.14/2.17  Reduction            : 0.41
% 6.14/2.17  Demodulation         : 0.32
% 6.14/2.17  BG Simplification    : 0.03
% 6.14/2.17  Subsumption          : 0.16
% 6.14/2.17  Abstraction          : 0.04
% 6.14/2.17  MUC search           : 0.00
% 6.14/2.17  Cooper               : 0.00
% 6.14/2.17  Total                : 1.41
% 6.14/2.17  Index Insertion      : 0.00
% 6.14/2.17  Index Deletion       : 0.00
% 6.14/2.17  Index Matching       : 0.00
% 6.14/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
