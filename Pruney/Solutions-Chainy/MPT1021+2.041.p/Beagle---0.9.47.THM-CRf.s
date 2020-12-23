%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:06 EST 2020

% Result     : Theorem 6.09s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 355 expanded)
%              Number of leaves         :   43 ( 153 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 (1065 expanded)
%              Number of equality atoms :   40 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

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

tff(f_142,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_51,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_119,axiom,(
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

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_72,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2413,plain,(
    ! [C_237,A_238,B_239] :
      ( v2_funct_1(C_237)
      | ~ v3_funct_2(C_237,A_238,B_239)
      | ~ v1_funct_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2419,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2413])).

tff(c_2427,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2419])).

tff(c_44,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_57,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_2447,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( r2_relset_1(A_245,B_246,C_247,C_247)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246)))
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2457,plain,(
    ! [A_249,C_250] :
      ( r2_relset_1(A_249,A_249,C_250,C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_249,A_249))) ) ),
    inference(resolution,[status(thm)],[c_57,c_2447])).

tff(c_2465,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_57,c_2457])).

tff(c_2219,plain,(
    ! [C_200,B_201,A_202] :
      ( v5_relat_1(C_200,B_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2231,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2219])).

tff(c_2236,plain,(
    ! [B_207,A_208] :
      ( k2_relat_1(B_207) = A_208
      | ~ v2_funct_2(B_207,A_208)
      | ~ v5_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2245,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2231,c_2236])).

tff(c_2254,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2245])).

tff(c_2255,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2254])).

tff(c_2328,plain,(
    ! [C_223,B_224,A_225] :
      ( v2_funct_2(C_223,B_224)
      | ~ v3_funct_2(C_223,A_225,B_224)
      | ~ v1_funct_1(C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2334,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2328])).

tff(c_2342,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2334])).

tff(c_2344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2255,c_2342])).

tff(c_2345,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2254])).

tff(c_6,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2533,plain,(
    ! [A_269,B_270] :
      ( k2_funct_2(A_269,B_270) = k2_funct_1(B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(k2_zfmisc_1(A_269,A_269)))
      | ~ v3_funct_2(B_270,A_269,A_269)
      | ~ v1_funct_2(B_270,A_269,A_269)
      | ~ v1_funct_1(B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2539,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2533])).

tff(c_2547,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2539])).

tff(c_2513,plain,(
    ! [A_261,B_262] :
      ( v1_funct_1(k2_funct_2(A_261,B_262))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k2_zfmisc_1(A_261,A_261)))
      | ~ v3_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2519,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2513])).

tff(c_2527,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2519])).

tff(c_2549,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2547,c_2527])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_funct_2(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2704,plain,(
    ! [F_282,C_281,B_283,A_280,E_284,D_279] :
      ( k1_partfun1(A_280,B_283,C_281,D_279,E_284,F_282) = k5_relat_1(E_284,F_282)
      | ~ m1_subset_1(F_282,k1_zfmisc_1(k2_zfmisc_1(C_281,D_279)))
      | ~ v1_funct_1(F_282)
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_280,B_283)))
      | ~ v1_funct_1(E_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2712,plain,(
    ! [A_280,B_283,E_284] :
      ( k1_partfun1(A_280,B_283,'#skF_2','#skF_2',E_284,'#skF_3') = k5_relat_1(E_284,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_280,B_283)))
      | ~ v1_funct_1(E_284) ) ),
    inference(resolution,[status(thm)],[c_50,c_2704])).

tff(c_2736,plain,(
    ! [A_285,B_286,E_287] :
      ( k1_partfun1(A_285,B_286,'#skF_2','#skF_2',E_287,'#skF_3') = k5_relat_1(E_287,'#skF_3')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2712])).

tff(c_3090,plain,(
    ! [A_298,B_299] :
      ( k1_partfun1(A_298,A_298,'#skF_2','#skF_2',k2_funct_2(A_298,B_299),'#skF_3') = k5_relat_1(k2_funct_2(A_298,B_299),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_298,B_299))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k2_zfmisc_1(A_298,A_298)))
      | ~ v3_funct_2(B_299,A_298,A_298)
      | ~ v1_funct_2(B_299,A_298,A_298)
      | ~ v1_funct_1(B_299) ) ),
    inference(resolution,[status(thm)],[c_32,c_2736])).

tff(c_3102,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3090])).

tff(c_3119,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2549,c_2547,c_2547,c_2547,c_3102])).

tff(c_300,plain,(
    ! [C_90,A_91,B_92] :
      ( v2_funct_1(C_90)
      | ~ v3_funct_2(C_90,A_91,B_92)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_306,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_300])).

tff(c_314,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_306])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_352,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_relset_1(A_100,B_101,C_102,C_102)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_371,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(resolution,[status(thm)],[c_4,c_352])).

tff(c_379,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_57,c_371])).

tff(c_245,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_257,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_334,plain,(
    ! [A_98,B_99] :
      ( k1_relset_1(A_98,A_98,B_99) = A_98
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_340,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_334])).

tff(c_349,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_257,c_340])).

tff(c_8,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_403,plain,(
    ! [A_116,B_117] :
      ( k2_funct_2(A_116,B_117) = k2_funct_1(B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k2_zfmisc_1(A_116,A_116)))
      | ~ v3_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_2(B_117,A_116,A_116)
      | ~ v1_funct_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_409,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_403])).

tff(c_417,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_409])).

tff(c_385,plain,(
    ! [A_111,B_112] :
      ( v1_funct_1(k2_funct_2(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_111,A_111)))
      | ~ v3_funct_2(B_112,A_111,A_111)
      | ~ v1_funct_2(B_112,A_111,A_111)
      | ~ v1_funct_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_391,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_385])).

tff(c_399,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_391])).

tff(c_419,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_399])).

tff(c_566,plain,(
    ! [D_130,C_132,A_131,E_135,F_133,B_134] :
      ( k1_partfun1(A_131,B_134,C_132,D_130,E_135,F_133) = k5_relat_1(E_135,F_133)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_132,D_130)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_131,B_134)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2068,plain,(
    ! [B_185,A_188,B_186,E_187,A_184] :
      ( k1_partfun1(A_184,B_185,A_188,A_188,E_187,k2_funct_2(A_188,B_186)) = k5_relat_1(E_187,k2_funct_2(A_188,B_186))
      | ~ v1_funct_1(k2_funct_2(A_188,B_186))
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_1(E_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_186,A_188,A_188)
      | ~ v1_funct_2(B_186,A_188,A_188)
      | ~ v1_funct_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_32,c_566])).

tff(c_2088,plain,(
    ! [A_188,B_186] :
      ( k1_partfun1('#skF_2','#skF_2',A_188,A_188,'#skF_3',k2_funct_2(A_188,B_186)) = k5_relat_1('#skF_3',k2_funct_2(A_188,B_186))
      | ~ v1_funct_1(k2_funct_2(A_188,B_186))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_186,A_188,A_188)
      | ~ v1_funct_2(B_186,A_188,A_188)
      | ~ v1_funct_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_50,c_2068])).

tff(c_2137,plain,(
    ! [A_189,B_190] :
      ( k1_partfun1('#skF_2','#skF_2',A_189,A_189,'#skF_3',k2_funct_2(A_189,B_190)) = k5_relat_1('#skF_3',k2_funct_2(A_189,B_190))
      | ~ v1_funct_1(k2_funct_2(A_189,B_190))
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2088])).

tff(c_2157,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2137])).

tff(c_2186,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_419,c_417,c_417,c_417,c_2157])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_86,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_420,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_86])).

tff(c_2188,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_420])).

tff(c_2195,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2188])).

tff(c_2198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_314,c_379,c_349,c_2195])).

tff(c_2199,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2551,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2547,c_2199])).

tff(c_3148,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_2551])).

tff(c_3155,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_3148])).

tff(c_3158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_56,c_2427,c_2465,c_2345,c_3155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.09/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.26  
% 6.09/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.09/2.26  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 6.09/2.26  
% 6.09/2.26  %Foreground sorts:
% 6.09/2.26  
% 6.09/2.26  
% 6.09/2.26  %Background operators:
% 6.09/2.26  
% 6.09/2.26  
% 6.09/2.26  %Foreground operators:
% 6.09/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.09/2.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.09/2.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.09/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.09/2.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.09/2.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.09/2.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.09/2.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.09/2.26  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.09/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.09/2.26  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.09/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.09/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.09/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.09/2.26  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.09/2.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.09/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.09/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.09/2.26  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.09/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.09/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.09/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.09/2.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.09/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.09/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.09/2.26  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.09/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.09/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.09/2.26  
% 6.42/2.28  tff(f_142, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 6.42/2.28  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.42/2.28  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.42/2.28  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.42/2.28  tff(f_63, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.42/2.28  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.42/2.28  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.42/2.28  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.42/2.28  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.42/2.28  tff(f_119, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.42/2.28  tff(f_99, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.42/2.28  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.42/2.28  tff(f_31, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 6.42/2.28  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.42/2.28  tff(f_129, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 6.42/2.28  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.42/2.28  tff(c_72, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.42/2.28  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_72])).
% 6.42/2.28  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.42/2.28  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.42/2.28  tff(c_2413, plain, (![C_237, A_238, B_239]: (v2_funct_1(C_237) | ~v3_funct_2(C_237, A_238, B_239) | ~v1_funct_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.28  tff(c_2419, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2413])).
% 6.42/2.28  tff(c_2427, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2419])).
% 6.42/2.28  tff(c_44, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.42/2.28  tff(c_20, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.42/2.28  tff(c_57, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 6.42/2.28  tff(c_2447, plain, (![A_245, B_246, C_247, D_248]: (r2_relset_1(A_245, B_246, C_247, C_247) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.42/2.28  tff(c_2457, plain, (![A_249, C_250]: (r2_relset_1(A_249, A_249, C_250, C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_249, A_249))))), inference(resolution, [status(thm)], [c_57, c_2447])).
% 6.42/2.28  tff(c_2465, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_57, c_2457])).
% 6.42/2.28  tff(c_2219, plain, (![C_200, B_201, A_202]: (v5_relat_1(C_200, B_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.42/2.28  tff(c_2231, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_2219])).
% 6.42/2.28  tff(c_2236, plain, (![B_207, A_208]: (k2_relat_1(B_207)=A_208 | ~v2_funct_2(B_207, A_208) | ~v5_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.42/2.28  tff(c_2245, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2231, c_2236])).
% 6.42/2.28  tff(c_2254, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2245])).
% 6.42/2.28  tff(c_2255, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2254])).
% 6.42/2.28  tff(c_2328, plain, (![C_223, B_224, A_225]: (v2_funct_2(C_223, B_224) | ~v3_funct_2(C_223, A_225, B_224) | ~v1_funct_1(C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.28  tff(c_2334, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2328])).
% 6.42/2.28  tff(c_2342, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2334])).
% 6.42/2.28  tff(c_2344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2255, c_2342])).
% 6.42/2.28  tff(c_2345, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2254])).
% 6.42/2.28  tff(c_6, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.42/2.28  tff(c_59, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 6.42/2.28  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.42/2.28  tff(c_2533, plain, (![A_269, B_270]: (k2_funct_2(A_269, B_270)=k2_funct_1(B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(k2_zfmisc_1(A_269, A_269))) | ~v3_funct_2(B_270, A_269, A_269) | ~v1_funct_2(B_270, A_269, A_269) | ~v1_funct_1(B_270))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.42/2.28  tff(c_2539, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2533])).
% 6.42/2.28  tff(c_2547, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2539])).
% 6.42/2.28  tff(c_2513, plain, (![A_261, B_262]: (v1_funct_1(k2_funct_2(A_261, B_262)) | ~m1_subset_1(B_262, k1_zfmisc_1(k2_zfmisc_1(A_261, A_261))) | ~v3_funct_2(B_262, A_261, A_261) | ~v1_funct_2(B_262, A_261, A_261) | ~v1_funct_1(B_262))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.42/2.28  tff(c_2519, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2513])).
% 6.42/2.28  tff(c_2527, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2519])).
% 6.42/2.28  tff(c_2549, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2547, c_2527])).
% 6.42/2.28  tff(c_32, plain, (![A_23, B_24]: (m1_subset_1(k2_funct_2(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.42/2.28  tff(c_2704, plain, (![F_282, C_281, B_283, A_280, E_284, D_279]: (k1_partfun1(A_280, B_283, C_281, D_279, E_284, F_282)=k5_relat_1(E_284, F_282) | ~m1_subset_1(F_282, k1_zfmisc_1(k2_zfmisc_1(C_281, D_279))) | ~v1_funct_1(F_282) | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_280, B_283))) | ~v1_funct_1(E_284))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.42/2.28  tff(c_2712, plain, (![A_280, B_283, E_284]: (k1_partfun1(A_280, B_283, '#skF_2', '#skF_2', E_284, '#skF_3')=k5_relat_1(E_284, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_280, B_283))) | ~v1_funct_1(E_284))), inference(resolution, [status(thm)], [c_50, c_2704])).
% 6.42/2.28  tff(c_2736, plain, (![A_285, B_286, E_287]: (k1_partfun1(A_285, B_286, '#skF_2', '#skF_2', E_287, '#skF_3')=k5_relat_1(E_287, '#skF_3') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2712])).
% 6.42/2.28  tff(c_3090, plain, (![A_298, B_299]: (k1_partfun1(A_298, A_298, '#skF_2', '#skF_2', k2_funct_2(A_298, B_299), '#skF_3')=k5_relat_1(k2_funct_2(A_298, B_299), '#skF_3') | ~v1_funct_1(k2_funct_2(A_298, B_299)) | ~m1_subset_1(B_299, k1_zfmisc_1(k2_zfmisc_1(A_298, A_298))) | ~v3_funct_2(B_299, A_298, A_298) | ~v1_funct_2(B_299, A_298, A_298) | ~v1_funct_1(B_299))), inference(resolution, [status(thm)], [c_32, c_2736])).
% 6.42/2.28  tff(c_3102, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_3090])).
% 6.42/2.28  tff(c_3119, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2549, c_2547, c_2547, c_2547, c_3102])).
% 6.42/2.28  tff(c_300, plain, (![C_90, A_91, B_92]: (v2_funct_1(C_90) | ~v3_funct_2(C_90, A_91, B_92) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.28  tff(c_306, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_300])).
% 6.42/2.28  tff(c_314, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_306])).
% 6.42/2.28  tff(c_4, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.28  tff(c_352, plain, (![A_100, B_101, C_102, D_103]: (r2_relset_1(A_100, B_101, C_102, C_102) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.42/2.28  tff(c_371, plain, (![A_104, B_105, C_106]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(resolution, [status(thm)], [c_4, c_352])).
% 6.42/2.28  tff(c_379, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_57, c_371])).
% 6.42/2.28  tff(c_245, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.42/2.28  tff(c_257, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_245])).
% 6.42/2.28  tff(c_334, plain, (![A_98, B_99]: (k1_relset_1(A_98, A_98, B_99)=A_98 | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.42/2.28  tff(c_340, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_334])).
% 6.42/2.28  tff(c_349, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_257, c_340])).
% 6.42/2.28  tff(c_8, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.42/2.28  tff(c_58, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 6.42/2.28  tff(c_403, plain, (![A_116, B_117]: (k2_funct_2(A_116, B_117)=k2_funct_1(B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(k2_zfmisc_1(A_116, A_116))) | ~v3_funct_2(B_117, A_116, A_116) | ~v1_funct_2(B_117, A_116, A_116) | ~v1_funct_1(B_117))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.42/2.28  tff(c_409, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_403])).
% 6.42/2.28  tff(c_417, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_409])).
% 6.42/2.28  tff(c_385, plain, (![A_111, B_112]: (v1_funct_1(k2_funct_2(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(A_111, A_111))) | ~v3_funct_2(B_112, A_111, A_111) | ~v1_funct_2(B_112, A_111, A_111) | ~v1_funct_1(B_112))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.42/2.28  tff(c_391, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_385])).
% 6.42/2.28  tff(c_399, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_391])).
% 6.42/2.28  tff(c_419, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_399])).
% 6.42/2.28  tff(c_566, plain, (![D_130, C_132, A_131, E_135, F_133, B_134]: (k1_partfun1(A_131, B_134, C_132, D_130, E_135, F_133)=k5_relat_1(E_135, F_133) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_132, D_130))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_131, B_134))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.42/2.28  tff(c_2068, plain, (![B_185, A_188, B_186, E_187, A_184]: (k1_partfun1(A_184, B_185, A_188, A_188, E_187, k2_funct_2(A_188, B_186))=k5_relat_1(E_187, k2_funct_2(A_188, B_186)) | ~v1_funct_1(k2_funct_2(A_188, B_186)) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_1(E_187) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_186, A_188, A_188) | ~v1_funct_2(B_186, A_188, A_188) | ~v1_funct_1(B_186))), inference(resolution, [status(thm)], [c_32, c_566])).
% 6.42/2.28  tff(c_2088, plain, (![A_188, B_186]: (k1_partfun1('#skF_2', '#skF_2', A_188, A_188, '#skF_3', k2_funct_2(A_188, B_186))=k5_relat_1('#skF_3', k2_funct_2(A_188, B_186)) | ~v1_funct_1(k2_funct_2(A_188, B_186)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_186, A_188, A_188) | ~v1_funct_2(B_186, A_188, A_188) | ~v1_funct_1(B_186))), inference(resolution, [status(thm)], [c_50, c_2068])).
% 6.42/2.28  tff(c_2137, plain, (![A_189, B_190]: (k1_partfun1('#skF_2', '#skF_2', A_189, A_189, '#skF_3', k2_funct_2(A_189, B_190))=k5_relat_1('#skF_3', k2_funct_2(A_189, B_190)) | ~v1_funct_1(k2_funct_2(A_189, B_190)) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2088])).
% 6.42/2.28  tff(c_2157, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2137])).
% 6.42/2.28  tff(c_2186, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_419, c_417, c_417, c_417, c_2157])).
% 6.42/2.28  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.42/2.28  tff(c_86, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 6.42/2.28  tff(c_420, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_86])).
% 6.42/2.28  tff(c_2188, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_420])).
% 6.42/2.28  tff(c_2195, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2188])).
% 6.42/2.28  tff(c_2198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_314, c_379, c_349, c_2195])).
% 6.42/2.28  tff(c_2199, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 6.42/2.28  tff(c_2551, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2547, c_2199])).
% 6.42/2.28  tff(c_3148, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_2551])).
% 6.42/2.28  tff(c_3155, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59, c_3148])).
% 6.42/2.28  tff(c_3158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_56, c_2427, c_2465, c_2345, c_3155])).
% 6.42/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.28  
% 6.42/2.28  Inference rules
% 6.42/2.28  ----------------------
% 6.42/2.28  #Ref     : 0
% 6.42/2.28  #Sup     : 669
% 6.42/2.28  #Fact    : 0
% 6.42/2.28  #Define  : 0
% 6.42/2.28  #Split   : 3
% 6.42/2.28  #Chain   : 0
% 6.42/2.28  #Close   : 0
% 6.42/2.28  
% 6.42/2.28  Ordering : KBO
% 6.42/2.28  
% 6.42/2.28  Simplification rules
% 6.42/2.28  ----------------------
% 6.42/2.28  #Subsume      : 6
% 6.42/2.28  #Demod        : 1469
% 6.42/2.28  #Tautology    : 264
% 6.42/2.28  #SimpNegUnit  : 2
% 6.42/2.28  #BackRed      : 56
% 6.42/2.28  
% 6.42/2.28  #Partial instantiations: 0
% 6.42/2.28  #Strategies tried      : 1
% 6.42/2.28  
% 6.42/2.28  Timing (in seconds)
% 6.42/2.28  ----------------------
% 6.42/2.28  Preprocessing        : 0.36
% 6.42/2.28  Parsing              : 0.19
% 6.42/2.28  CNF conversion       : 0.02
% 6.42/2.28  Main loop            : 1.14
% 6.42/2.29  Inferencing          : 0.37
% 6.42/2.29  Reduction            : 0.46
% 6.42/2.29  Demodulation         : 0.35
% 6.42/2.29  BG Simplification    : 0.04
% 6.42/2.29  Subsumption          : 0.18
% 6.42/2.29  Abstraction          : 0.05
% 6.42/2.29  MUC search           : 0.00
% 6.42/2.29  Cooper               : 0.00
% 6.42/2.29  Total                : 1.55
% 6.42/2.29  Index Insertion      : 0.00
% 6.42/2.29  Index Deletion       : 0.00
% 6.42/2.29  Index Matching       : 0.00
% 6.42/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
