%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:10 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.01s
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

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_146,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_99,axiom,(
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

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2403,plain,(
    ! [B_192,A_193] :
      ( v1_relat_1(B_192)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(A_193))
      | ~ v1_relat_1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2409,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_2403])).

tff(c_2419,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2409])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2612,plain,(
    ! [C_232,A_233,B_234] :
      ( v2_funct_1(C_232)
      | ~ v3_funct_2(C_232,A_233,B_234)
      | ~ v1_funct_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2618,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2612])).

tff(c_2626,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2618])).

tff(c_40,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2682,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( r2_relset_1(A_244,B_245,C_246,C_246)
      | ~ m1_subset_1(D_247,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2692,plain,(
    ! [A_248,C_249] :
      ( r2_relset_1(A_248,A_248,C_249,C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,A_248))) ) ),
    inference(resolution,[status(thm)],[c_40,c_2682])).

tff(c_2700,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_40,c_2692])).

tff(c_2439,plain,(
    ! [C_202,B_203,A_204] :
      ( v5_relat_1(C_202,B_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2451,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2439])).

tff(c_2456,plain,(
    ! [B_209,A_210] :
      ( k2_relat_1(B_209) = A_210
      | ~ v2_funct_2(B_209,A_210)
      | ~ v5_relat_1(B_209,A_210)
      | ~ v1_relat_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2465,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2451,c_2456])).

tff(c_2472,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_2465])).

tff(c_2473,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2472])).

tff(c_2537,plain,(
    ! [C_222,B_223,A_224] :
      ( v2_funct_2(C_222,B_223)
      | ~ v3_funct_2(C_222,A_224,B_223)
      | ~ v1_funct_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2543,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2537])).

tff(c_2551,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2543])).

tff(c_2553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2473,c_2551])).

tff(c_2554,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2472])).

tff(c_46,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_partfun1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2735,plain,(
    ! [A_259,B_260] :
      ( k2_funct_2(A_259,B_260) = k2_funct_1(B_260)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(k2_zfmisc_1(A_259,A_259)))
      | ~ v3_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_2(B_260,A_259,A_259)
      | ~ v1_funct_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2741,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2735])).

tff(c_2749,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2741])).

tff(c_2717,plain,(
    ! [A_254,B_255] :
      ( v1_funct_1(k2_funct_2(A_254,B_255))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k2_zfmisc_1(A_254,A_254)))
      | ~ v3_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_2(B_255,A_254,A_254)
      | ~ v1_funct_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2723,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2717])).

tff(c_2731,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2723])).

tff(c_2751,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_2731])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_funct_2(A_24,B_25),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2925,plain,(
    ! [B_279,E_278,A_280,F_275,D_277,C_276] :
      ( k1_partfun1(A_280,B_279,C_276,D_277,E_278,F_275) = k5_relat_1(E_278,F_275)
      | ~ m1_subset_1(F_275,k1_zfmisc_1(k2_zfmisc_1(C_276,D_277)))
      | ~ v1_funct_1(F_275)
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279)))
      | ~ v1_funct_1(E_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2933,plain,(
    ! [A_280,B_279,E_278] :
      ( k1_partfun1(A_280,B_279,'#skF_2','#skF_2',E_278,'#skF_3') = k5_relat_1(E_278,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(A_280,B_279)))
      | ~ v1_funct_1(E_278) ) ),
    inference(resolution,[status(thm)],[c_52,c_2925])).

tff(c_2947,plain,(
    ! [A_281,B_282,E_283] :
      ( k1_partfun1(A_281,B_282,'#skF_2','#skF_2',E_283,'#skF_3') = k5_relat_1(E_283,'#skF_3')
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ v1_funct_1(E_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2933])).

tff(c_3312,plain,(
    ! [A_294,B_295] :
      ( k1_partfun1(A_294,A_294,'#skF_2','#skF_2',k2_funct_2(A_294,B_295),'#skF_3') = k5_relat_1(k2_funct_2(A_294,B_295),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_294,B_295))
      | ~ m1_subset_1(B_295,k1_zfmisc_1(k2_zfmisc_1(A_294,A_294)))
      | ~ v3_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_2(B_295,A_294,A_294)
      | ~ v1_funct_1(B_295) ) ),
    inference(resolution,[status(thm)],[c_30,c_2947])).

tff(c_3324,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3312])).

tff(c_3341,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2751,c_2749,c_2749,c_2749,c_3324])).

tff(c_75,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_81])).

tff(c_275,plain,(
    ! [C_83,A_84,B_85] :
      ( v2_funct_1(C_83)
      | ~ v3_funct_2(C_83,A_84,B_85)
      | ~ v1_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_281,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_275])).

tff(c_289,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_281])).

tff(c_318,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( r2_relset_1(A_93,B_94,C_95,C_95)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_328,plain,(
    ! [A_97,C_98] :
      ( r2_relset_1(A_97,A_97,C_98,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97))) ) ),
    inference(resolution,[status(thm)],[c_40,c_318])).

tff(c_336,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_40,c_328])).

tff(c_145,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_157,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_145])).

tff(c_340,plain,(
    ! [A_100,B_101] :
      ( k1_relset_1(A_100,A_100,B_101) = A_100
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100)))
      | ~ v1_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_346,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_340])).

tff(c_355,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_157,c_346])).

tff(c_10,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_399,plain,(
    ! [A_110,B_111] :
      ( k2_funct_2(A_110,B_111) = k2_funct_1(B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v3_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_2(B_111,A_110,A_110)
      | ~ v1_funct_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_405,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_399])).

tff(c_413,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_405])).

tff(c_383,plain,(
    ! [A_108,B_109] :
      ( v1_funct_1(k2_funct_2(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_389,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_383])).

tff(c_397,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_389])).

tff(c_415,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_397])).

tff(c_567,plain,(
    ! [A_131,E_129,B_130,F_126,C_127,D_128] :
      ( k1_partfun1(A_131,B_130,C_127,D_128,E_129,F_126) = k5_relat_1(E_129,F_126)
      | ~ m1_subset_1(F_126,k1_zfmisc_1(k2_zfmisc_1(C_127,D_128)))
      | ~ v1_funct_1(F_126)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130)))
      | ~ v1_funct_1(E_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2268,plain,(
    ! [E_188,A_185,B_186,A_189,B_187] :
      ( k1_partfun1(A_185,B_186,A_189,A_189,E_188,k2_funct_2(A_189,B_187)) = k5_relat_1(E_188,k2_funct_2(A_189,B_187))
      | ~ v1_funct_1(k2_funct_2(A_189,B_187))
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ v1_funct_1(E_188)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_187,A_189,A_189)
      | ~ v1_funct_2(B_187,A_189,A_189)
      | ~ v1_funct_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_30,c_567])).

tff(c_2290,plain,(
    ! [A_189,B_187] :
      ( k1_partfun1('#skF_2','#skF_2',A_189,A_189,'#skF_3',k2_funct_2(A_189,B_187)) = k5_relat_1('#skF_3',k2_funct_2(A_189,B_187))
      | ~ v1_funct_1(k2_funct_2(A_189,B_187))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_187,A_189,A_189)
      | ~ v1_funct_2(B_187,A_189,A_189)
      | ~ v1_funct_1(B_187) ) ),
    inference(resolution,[status(thm)],[c_52,c_2268])).

tff(c_2334,plain,(
    ! [A_190,B_191] :
      ( k1_partfun1('#skF_2','#skF_2',A_190,A_190,'#skF_3',k2_funct_2(A_190,B_191)) = k5_relat_1('#skF_3',k2_funct_2(A_190,B_191))
      | ~ v1_funct_1(k2_funct_2(A_190,B_191))
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_190,A_190)))
      | ~ v3_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_2(B_191,A_190,A_190)
      | ~ v1_funct_1(B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2290])).

tff(c_2356,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_2334])).

tff(c_2388,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_415,c_413,c_413,c_413,c_2356])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_416,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_74])).

tff(c_2390,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_416])).

tff(c_2397,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2390])).

tff(c_2400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_58,c_289,c_336,c_355,c_2397])).

tff(c_2401,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2753,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_2401])).

tff(c_3370,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3341,c_2753])).

tff(c_3377,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3370])).

tff(c_3380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2419,c_58,c_2626,c_2700,c_2554,c_3377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:34:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.19  
% 6.01/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.19  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 6.01/2.19  
% 6.01/2.19  %Foreground sorts:
% 6.01/2.19  
% 6.01/2.19  
% 6.01/2.19  %Background operators:
% 6.01/2.19  
% 6.01/2.19  
% 6.01/2.19  %Foreground operators:
% 6.01/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.01/2.19  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.01/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.01/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.01/2.19  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.01/2.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.01/2.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.01/2.19  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.01/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.01/2.19  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.01/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.01/2.19  tff('#skF_2', type, '#skF_2': $i).
% 6.01/2.19  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.01/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.01/2.19  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.01/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.01/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.01/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.01/2.19  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.01/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.01/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.01/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.01/2.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.01/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.01/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.01/2.19  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.01/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.01/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.01/2.19  
% 6.01/2.21  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.01/2.21  tff(f_146, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 6.01/2.21  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.01/2.21  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.01/2.21  tff(f_103, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.01/2.21  tff(f_63, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.01/2.21  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.01/2.21  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.01/2.21  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.01/2.21  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.01/2.21  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.01/2.21  tff(f_99, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.01/2.21  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.01/2.21  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.01/2.21  tff(f_133, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 6.01/2.21  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.01/2.21  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.01/2.21  tff(c_2403, plain, (![B_192, A_193]: (v1_relat_1(B_192) | ~m1_subset_1(B_192, k1_zfmisc_1(A_193)) | ~v1_relat_1(A_193))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.01/2.21  tff(c_2409, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_2403])).
% 6.01/2.21  tff(c_2419, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2409])).
% 6.01/2.21  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.01/2.21  tff(c_54, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.01/2.21  tff(c_2612, plain, (![C_232, A_233, B_234]: (v2_funct_1(C_232) | ~v3_funct_2(C_232, A_233, B_234) | ~v1_funct_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.01/2.21  tff(c_2618, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2612])).
% 6.01/2.21  tff(c_2626, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2618])).
% 6.01/2.21  tff(c_40, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.01/2.21  tff(c_2682, plain, (![A_244, B_245, C_246, D_247]: (r2_relset_1(A_244, B_245, C_246, C_246) | ~m1_subset_1(D_247, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.01/2.21  tff(c_2692, plain, (![A_248, C_249]: (r2_relset_1(A_248, A_248, C_249, C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, A_248))))), inference(resolution, [status(thm)], [c_40, c_2682])).
% 6.01/2.21  tff(c_2700, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_40, c_2692])).
% 6.01/2.21  tff(c_2439, plain, (![C_202, B_203, A_204]: (v5_relat_1(C_202, B_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.01/2.21  tff(c_2451, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_2439])).
% 6.01/2.21  tff(c_2456, plain, (![B_209, A_210]: (k2_relat_1(B_209)=A_210 | ~v2_funct_2(B_209, A_210) | ~v5_relat_1(B_209, A_210) | ~v1_relat_1(B_209))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.01/2.21  tff(c_2465, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2451, c_2456])).
% 6.01/2.21  tff(c_2472, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2419, c_2465])).
% 6.01/2.21  tff(c_2473, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2472])).
% 6.01/2.21  tff(c_2537, plain, (![C_222, B_223, A_224]: (v2_funct_2(C_222, B_223) | ~v3_funct_2(C_222, A_224, B_223) | ~v1_funct_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.01/2.21  tff(c_2543, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2537])).
% 6.01/2.21  tff(c_2551, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2543])).
% 6.01/2.21  tff(c_2553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2473, c_2551])).
% 6.01/2.21  tff(c_2554, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2472])).
% 6.01/2.21  tff(c_46, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.01/2.21  tff(c_8, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.01/2.21  tff(c_60, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_partfun1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 6.01/2.21  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.01/2.21  tff(c_2735, plain, (![A_259, B_260]: (k2_funct_2(A_259, B_260)=k2_funct_1(B_260) | ~m1_subset_1(B_260, k1_zfmisc_1(k2_zfmisc_1(A_259, A_259))) | ~v3_funct_2(B_260, A_259, A_259) | ~v1_funct_2(B_260, A_259, A_259) | ~v1_funct_1(B_260))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.21  tff(c_2741, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2735])).
% 6.01/2.21  tff(c_2749, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2741])).
% 6.01/2.21  tff(c_2717, plain, (![A_254, B_255]: (v1_funct_1(k2_funct_2(A_254, B_255)) | ~m1_subset_1(B_255, k1_zfmisc_1(k2_zfmisc_1(A_254, A_254))) | ~v3_funct_2(B_255, A_254, A_254) | ~v1_funct_2(B_255, A_254, A_254) | ~v1_funct_1(B_255))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.01/2.21  tff(c_2723, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2717])).
% 6.01/2.21  tff(c_2731, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2723])).
% 6.01/2.21  tff(c_2751, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_2731])).
% 6.01/2.21  tff(c_30, plain, (![A_24, B_25]: (m1_subset_1(k2_funct_2(A_24, B_25), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.01/2.21  tff(c_2925, plain, (![B_279, E_278, A_280, F_275, D_277, C_276]: (k1_partfun1(A_280, B_279, C_276, D_277, E_278, F_275)=k5_relat_1(E_278, F_275) | ~m1_subset_1(F_275, k1_zfmisc_1(k2_zfmisc_1(C_276, D_277))) | ~v1_funct_1(F_275) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))) | ~v1_funct_1(E_278))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.01/2.21  tff(c_2933, plain, (![A_280, B_279, E_278]: (k1_partfun1(A_280, B_279, '#skF_2', '#skF_2', E_278, '#skF_3')=k5_relat_1(E_278, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(A_280, B_279))) | ~v1_funct_1(E_278))), inference(resolution, [status(thm)], [c_52, c_2925])).
% 6.01/2.21  tff(c_2947, plain, (![A_281, B_282, E_283]: (k1_partfun1(A_281, B_282, '#skF_2', '#skF_2', E_283, '#skF_3')=k5_relat_1(E_283, '#skF_3') | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~v1_funct_1(E_283))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2933])).
% 6.01/2.21  tff(c_3312, plain, (![A_294, B_295]: (k1_partfun1(A_294, A_294, '#skF_2', '#skF_2', k2_funct_2(A_294, B_295), '#skF_3')=k5_relat_1(k2_funct_2(A_294, B_295), '#skF_3') | ~v1_funct_1(k2_funct_2(A_294, B_295)) | ~m1_subset_1(B_295, k1_zfmisc_1(k2_zfmisc_1(A_294, A_294))) | ~v3_funct_2(B_295, A_294, A_294) | ~v1_funct_2(B_295, A_294, A_294) | ~v1_funct_1(B_295))), inference(resolution, [status(thm)], [c_30, c_2947])).
% 6.01/2.21  tff(c_3324, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_3312])).
% 6.01/2.21  tff(c_3341, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2751, c_2749, c_2749, c_2749, c_3324])).
% 6.01/2.21  tff(c_75, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.01/2.21  tff(c_81, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_75])).
% 6.01/2.21  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_81])).
% 6.01/2.21  tff(c_275, plain, (![C_83, A_84, B_85]: (v2_funct_1(C_83) | ~v3_funct_2(C_83, A_84, B_85) | ~v1_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.01/2.21  tff(c_281, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_275])).
% 6.01/2.21  tff(c_289, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_281])).
% 6.01/2.21  tff(c_318, plain, (![A_93, B_94, C_95, D_96]: (r2_relset_1(A_93, B_94, C_95, C_95) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.01/2.21  tff(c_328, plain, (![A_97, C_98]: (r2_relset_1(A_97, A_97, C_98, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))))), inference(resolution, [status(thm)], [c_40, c_318])).
% 6.01/2.21  tff(c_336, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_40, c_328])).
% 6.01/2.21  tff(c_145, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.01/2.21  tff(c_157, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_145])).
% 6.01/2.21  tff(c_340, plain, (![A_100, B_101]: (k1_relset_1(A_100, A_100, B_101)=A_100 | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))) | ~v1_funct_2(B_101, A_100, A_100) | ~v1_funct_1(B_101))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.01/2.21  tff(c_346, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_340])).
% 6.01/2.21  tff(c_355, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_157, c_346])).
% 6.01/2.21  tff(c_10, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.01/2.21  tff(c_59, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 6.01/2.21  tff(c_399, plain, (![A_110, B_111]: (k2_funct_2(A_110, B_111)=k2_funct_1(B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v3_funct_2(B_111, A_110, A_110) | ~v1_funct_2(B_111, A_110, A_110) | ~v1_funct_1(B_111))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.21  tff(c_405, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_399])).
% 6.01/2.21  tff(c_413, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_405])).
% 6.01/2.21  tff(c_383, plain, (![A_108, B_109]: (v1_funct_1(k2_funct_2(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.01/2.21  tff(c_389, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_383])).
% 6.01/2.21  tff(c_397, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_389])).
% 6.01/2.21  tff(c_415, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_397])).
% 6.01/2.21  tff(c_567, plain, (![A_131, E_129, B_130, F_126, C_127, D_128]: (k1_partfun1(A_131, B_130, C_127, D_128, E_129, F_126)=k5_relat_1(E_129, F_126) | ~m1_subset_1(F_126, k1_zfmisc_1(k2_zfmisc_1(C_127, D_128))) | ~v1_funct_1(F_126) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))) | ~v1_funct_1(E_129))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.01/2.21  tff(c_2268, plain, (![E_188, A_185, B_186, A_189, B_187]: (k1_partfun1(A_185, B_186, A_189, A_189, E_188, k2_funct_2(A_189, B_187))=k5_relat_1(E_188, k2_funct_2(A_189, B_187)) | ~v1_funct_1(k2_funct_2(A_189, B_187)) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~v1_funct_1(E_188) | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_187, A_189, A_189) | ~v1_funct_2(B_187, A_189, A_189) | ~v1_funct_1(B_187))), inference(resolution, [status(thm)], [c_30, c_567])).
% 6.01/2.21  tff(c_2290, plain, (![A_189, B_187]: (k1_partfun1('#skF_2', '#skF_2', A_189, A_189, '#skF_3', k2_funct_2(A_189, B_187))=k5_relat_1('#skF_3', k2_funct_2(A_189, B_187)) | ~v1_funct_1(k2_funct_2(A_189, B_187)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_187, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_187, A_189, A_189) | ~v1_funct_2(B_187, A_189, A_189) | ~v1_funct_1(B_187))), inference(resolution, [status(thm)], [c_52, c_2268])).
% 6.01/2.21  tff(c_2334, plain, (![A_190, B_191]: (k1_partfun1('#skF_2', '#skF_2', A_190, A_190, '#skF_3', k2_funct_2(A_190, B_191))=k5_relat_1('#skF_3', k2_funct_2(A_190, B_191)) | ~v1_funct_1(k2_funct_2(A_190, B_191)) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_190, A_190))) | ~v3_funct_2(B_191, A_190, A_190) | ~v1_funct_2(B_191, A_190, A_190) | ~v1_funct_1(B_191))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2290])).
% 6.01/2.21  tff(c_2356, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_2334])).
% 6.01/2.21  tff(c_2388, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_415, c_413, c_413, c_413, c_2356])).
% 6.01/2.21  tff(c_50, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.01/2.21  tff(c_74, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 6.01/2.21  tff(c_416, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_74])).
% 6.01/2.21  tff(c_2390, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_416])).
% 6.01/2.21  tff(c_2397, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59, c_2390])).
% 6.01/2.21  tff(c_2400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_58, c_289, c_336, c_355, c_2397])).
% 6.01/2.21  tff(c_2401, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 6.01/2.21  tff(c_2753, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_2401])).
% 6.01/2.21  tff(c_3370, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3341, c_2753])).
% 6.01/2.21  tff(c_3377, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60, c_3370])).
% 6.01/2.21  tff(c_3380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2419, c_58, c_2626, c_2700, c_2554, c_3377])).
% 6.01/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.21  
% 6.01/2.21  Inference rules
% 6.01/2.21  ----------------------
% 6.01/2.21  #Ref     : 0
% 6.01/2.21  #Sup     : 708
% 6.01/2.21  #Fact    : 0
% 6.01/2.21  #Define  : 0
% 6.01/2.21  #Split   : 3
% 6.01/2.21  #Chain   : 0
% 6.01/2.21  #Close   : 0
% 6.01/2.21  
% 6.01/2.21  Ordering : KBO
% 6.01/2.21  
% 6.01/2.21  Simplification rules
% 6.01/2.21  ----------------------
% 6.01/2.21  #Subsume      : 6
% 6.01/2.21  #Demod        : 1631
% 6.01/2.21  #Tautology    : 283
% 6.01/2.21  #SimpNegUnit  : 2
% 6.01/2.21  #BackRed      : 68
% 6.01/2.21  
% 6.01/2.21  #Partial instantiations: 0
% 6.01/2.21  #Strategies tried      : 1
% 6.01/2.21  
% 6.01/2.21  Timing (in seconds)
% 6.01/2.21  ----------------------
% 6.26/2.22  Preprocessing        : 0.34
% 6.26/2.22  Parsing              : 0.18
% 6.26/2.22  CNF conversion       : 0.02
% 6.26/2.22  Main loop            : 1.10
% 6.26/2.22  Inferencing          : 0.35
% 6.26/2.22  Reduction            : 0.45
% 6.26/2.22  Demodulation         : 0.35
% 6.26/2.22  BG Simplification    : 0.03
% 6.26/2.22  Subsumption          : 0.18
% 6.26/2.22  Abstraction          : 0.04
% 6.26/2.22  MUC search           : 0.00
% 6.26/2.22  Cooper               : 0.00
% 6.26/2.22  Total                : 1.49
% 6.26/2.22  Index Insertion      : 0.00
% 6.26/2.22  Index Deletion       : 0.00
% 6.26/2.22  Index Matching       : 0.00
% 6.26/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
