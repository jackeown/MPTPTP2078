%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:36 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 924 expanded)
%              Number of leaves         :   34 ( 302 expanded)
%              Depth                    :   12
%              Number of atoms          :  256 (2914 expanded)
%              Number of equality atoms :   89 (1112 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_129,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_137,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_129])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3003,plain,(
    ! [A_472,B_473,C_474] :
      ( k1_relset_1(A_472,B_473,C_474) = k1_relat_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3017,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3003])).

tff(c_3386,plain,(
    ! [B_521,A_522,C_523] :
      ( k1_xboole_0 = B_521
      | k1_relset_1(A_522,B_521,C_523) = A_522
      | ~ v1_funct_2(C_523,A_522,B_521)
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_522,B_521))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3395,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_3386])).

tff(c_3409,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3017,c_3395])).

tff(c_3410,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3409])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,A_10)) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3428,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3410,c_20])).

tff(c_3434,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_3428])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3293,plain,(
    ! [A_514,B_515,C_516,D_517] :
      ( k2_partfun1(A_514,B_515,C_516,D_517) = k7_relat_1(C_516,D_517)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515)))
      | ~ v1_funct_1(C_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3299,plain,(
    ! [D_517] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_517) = k7_relat_1('#skF_4',D_517)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_3293])).

tff(c_3312,plain,(
    ! [D_517] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_517) = k7_relat_1('#skF_4',D_517) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3299])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1031,plain,(
    ! [A_223,B_224,C_225] :
      ( k1_relset_1(A_223,B_224,C_225) = k1_relat_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1041,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1031])).

tff(c_1377,plain,(
    ! [B_275,A_276,C_277] :
      ( k1_xboole_0 = B_275
      | k1_relset_1(A_276,B_275,C_277) = A_276
      | ~ v1_funct_2(C_277,A_276,B_275)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_276,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1386,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1377])).

tff(c_1401,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1041,c_1386])).

tff(c_1402,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1401])).

tff(c_1415,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1402,c_20])).

tff(c_1421,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1415])).

tff(c_1224,plain,(
    ! [A_261,B_262,C_263,D_264] :
      ( k2_partfun1(A_261,B_262,C_263,D_264) = k7_relat_1(C_263,D_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_1(C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1228,plain,(
    ! [D_264] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_264) = k7_relat_1('#skF_4',D_264)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1224])).

tff(c_1237,plain,(
    ! [D_264] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_264) = k7_relat_1('#skF_4',D_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1228])).

tff(c_1613,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( m1_subset_1(k2_partfun1(A_293,B_294,C_295,D_296),k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ v1_funct_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1642,plain,(
    ! [D_264] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_264),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1237,c_1613])).

tff(c_1663,plain,(
    ! [D_297] : m1_subset_1(k7_relat_1('#skF_4',D_297),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1642])).

tff(c_30,plain,(
    ! [D_24,B_22,C_23,A_21] :
      ( m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(B_22,C_23)))
      | ~ r1_tarski(k1_relat_1(D_24),B_22)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_21,C_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2430,plain,(
    ! [D_409,B_410] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_409),k1_zfmisc_1(k2_zfmisc_1(B_410,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_409)),B_410) ) ),
    inference(resolution,[status(thm)],[c_1663,c_30])).

tff(c_274,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( v1_funct_1(k2_partfun1(A_87,B_88,C_89,D_90))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_276,plain,(
    ! [D_90] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_90))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_274])).

tff(c_283,plain,(
    ! [D_90] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_276])).

tff(c_52,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_139,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_139])).

tff(c_287,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_505,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_1239,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_505])).

tff(c_2487,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2430,c_1239])).

tff(c_2503,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1421,c_2487])).

tff(c_2506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6,c_2503])).

tff(c_2508,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_3016,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2508,c_3003])).

tff(c_3315,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3312,c_3312,c_3016])).

tff(c_2507,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_3321,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3312,c_2507])).

tff(c_3320,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3312,c_2508])).

tff(c_3500,plain,(
    ! [B_528,C_529,A_530] :
      ( k1_xboole_0 = B_528
      | v1_funct_2(C_529,A_530,B_528)
      | k1_relset_1(A_530,B_528,C_529) != A_530
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_530,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3506,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3320,c_3500])).

tff(c_3521,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3321,c_70,c_3506])).

tff(c_3748,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3315,c_3521])).

tff(c_3755,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3434,c_3748])).

tff(c_3759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3755])).

tff(c_3760,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3774,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_3760,c_14])).

tff(c_3761,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3767,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_3761])).

tff(c_3782,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3774,c_3767,c_58])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3783,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_3760,c_12])).

tff(c_3812,plain,(
    ! [C_554,A_555,B_556] :
      ( v1_relat_1(C_554)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_555,B_556))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3859,plain,(
    ! [C_560] :
      ( v1_relat_1(C_560)
      | ~ m1_subset_1(C_560,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_3812])).

tff(c_3863,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3782,c_3859])).

tff(c_4352,plain,(
    ! [C_666,A_667,B_668] :
      ( v4_relat_1(C_666,A_667)
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4359,plain,(
    ! [C_669,A_670] :
      ( v4_relat_1(C_669,A_670)
      | ~ m1_subset_1(C_669,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_4352])).

tff(c_4363,plain,(
    ! [A_671] : v4_relat_1('#skF_4',A_671) ),
    inference(resolution,[status(thm)],[c_3782,c_4359])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4366,plain,(
    ! [A_671] :
      ( k7_relat_1('#skF_4',A_671) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4363,c_16])).

tff(c_4369,plain,(
    ! [A_671] : k7_relat_1('#skF_4',A_671) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3863,c_4366])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3762,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_8])).

tff(c_4637,plain,(
    ! [B_719,A_720] :
      ( k1_relat_1(k7_relat_1(B_719,A_720)) = A_720
      | ~ r1_tarski(A_720,k1_relat_1(B_719))
      | ~ v1_relat_1(B_719) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5001,plain,(
    ! [B_779] :
      ( k1_relat_1(k7_relat_1(B_779,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_779) ) ),
    inference(resolution,[status(thm)],[c_3762,c_4637])).

tff(c_5014,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4369,c_5001])).

tff(c_5022,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3863,c_5014])).

tff(c_5136,plain,(
    ! [A_787,B_788,C_789] :
      ( k1_relset_1(A_787,B_788,C_789) = k1_relat_1(C_789)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(A_787,B_788))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5195,plain,(
    ! [B_797,C_798] :
      ( k1_relset_1('#skF_1',B_797,C_798) = k1_relat_1(C_798)
      | ~ m1_subset_1(C_798,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3774,c_5136])).

tff(c_5201,plain,(
    ! [B_797] : k1_relset_1('#skF_1',B_797,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3782,c_5195])).

tff(c_5206,plain,(
    ! [B_797] : k1_relset_1('#skF_1',B_797,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5022,c_5201])).

tff(c_38,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_5283,plain,(
    ! [C_802,B_803] :
      ( v1_funct_2(C_802,'#skF_1',B_803)
      | k1_relset_1('#skF_1',B_803,C_802) != '#skF_1'
      | ~ m1_subset_1(C_802,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3760,c_3760,c_3760,c_3760,c_63])).

tff(c_5289,plain,(
    ! [B_803] :
      ( v1_funct_2('#skF_4','#skF_1',B_803)
      | k1_relset_1('#skF_1',B_803,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_3782,c_5283])).

tff(c_5296,plain,(
    ! [B_803] : v1_funct_2('#skF_4','#skF_1',B_803) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5206,c_5289])).

tff(c_5403,plain,(
    ! [A_833,B_834,C_835,D_836] :
      ( k2_partfun1(A_833,B_834,C_835,D_836) = k7_relat_1(C_835,D_836)
      | ~ m1_subset_1(C_835,k1_zfmisc_1(k2_zfmisc_1(A_833,B_834)))
      | ~ v1_funct_1(C_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5408,plain,(
    ! [A_837,C_838,D_839] :
      ( k2_partfun1(A_837,'#skF_1',C_838,D_839) = k7_relat_1(C_838,D_839)
      | ~ m1_subset_1(C_838,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_838) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_5403])).

tff(c_5414,plain,(
    ! [A_837,D_839] :
      ( k2_partfun1(A_837,'#skF_1','#skF_4',D_839) = k7_relat_1('#skF_4',D_839)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3782,c_5408])).

tff(c_5422,plain,(
    ! [A_837,D_839] : k2_partfun1(A_837,'#skF_1','#skF_4',D_839) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4369,c_5414])).

tff(c_4975,plain,(
    ! [A_772,B_773,C_774,D_775] :
      ( k2_partfun1(A_772,B_773,C_774,D_775) = k7_relat_1(C_774,D_775)
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1(A_772,B_773)))
      | ~ v1_funct_1(C_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4983,plain,(
    ! [A_776,C_777,D_778] :
      ( k2_partfun1(A_776,'#skF_1',C_777,D_778) = k7_relat_1(C_777,D_778)
      | ~ m1_subset_1(C_777,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_777) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_4975])).

tff(c_4987,plain,(
    ! [A_776,D_778] :
      ( k2_partfun1(A_776,'#skF_1','#skF_4',D_778) = k7_relat_1('#skF_4',D_778)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3782,c_4983])).

tff(c_4992,plain,(
    ! [A_776,D_778] : k2_partfun1(A_776,'#skF_1','#skF_4',D_778) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4369,c_4987])).

tff(c_4051,plain,(
    ! [A_594,B_595,C_596,D_597] :
      ( v1_funct_1(k2_partfun1(A_594,B_595,C_596,D_597))
      | ~ m1_subset_1(C_596,k1_zfmisc_1(k2_zfmisc_1(A_594,B_595)))
      | ~ v1_funct_1(C_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4056,plain,(
    ! [A_598,C_599,D_600] :
      ( v1_funct_1(k2_partfun1(A_598,'#skF_1',C_599,D_600))
      | ~ m1_subset_1(C_599,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3783,c_4051])).

tff(c_4058,plain,(
    ! [A_598,D_600] :
      ( v1_funct_1(k2_partfun1(A_598,'#skF_1','#skF_4',D_600))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3782,c_4056])).

tff(c_4061,plain,(
    ! [A_598,D_600] : v1_funct_1(k2_partfun1(A_598,'#skF_1','#skF_4',D_600)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4058])).

tff(c_3817,plain,(
    ! [B_557,A_558] :
      ( B_557 = A_558
      | ~ r1_tarski(B_557,A_558)
      | ~ r1_tarski(A_558,B_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3825,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_3817])).

tff(c_3834,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3762,c_3825])).

tff(c_3864,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3834,c_3767,c_3834,c_3834,c_3767,c_3767,c_3834,c_3783,c_3767,c_3767,c_52])).

tff(c_3865,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3864])).

tff(c_4064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4061,c_3865])).

tff(c_4065,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3864])).

tff(c_4653,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4065])).

tff(c_4994,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4992,c_4653])).

tff(c_4998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3782,c_4994])).

tff(c_4999,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4065])).

tff(c_5434,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5422,c_4999])).

tff(c_5448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5296,c_5434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.12  
% 5.94/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.94/2.13  
% 5.94/2.13  %Foreground sorts:
% 5.94/2.13  
% 5.94/2.13  
% 5.94/2.13  %Background operators:
% 5.94/2.13  
% 5.94/2.13  
% 5.94/2.13  %Foreground operators:
% 5.94/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.94/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.94/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.94/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.94/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.94/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.94/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.94/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.94/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.94/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.94/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.13  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.94/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.94/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.94/2.13  
% 5.94/2.15  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 5.94/2.15  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.94/2.15  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.94/2.15  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.94/2.15  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 5.94/2.15  tff(f_113, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.94/2.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.94/2.15  tff(f_107, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.94/2.15  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.94/2.15  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.94/2.15  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.94/2.15  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.94/2.15  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.94/2.15  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.94/2.15  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.94/2.15  tff(c_129, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.15  tff(c_137, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_129])).
% 5.94/2.15  tff(c_54, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.94/2.15  tff(c_70, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 5.94/2.15  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.94/2.15  tff(c_3003, plain, (![A_472, B_473, C_474]: (k1_relset_1(A_472, B_473, C_474)=k1_relat_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.94/2.15  tff(c_3017, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3003])).
% 5.94/2.15  tff(c_3386, plain, (![B_521, A_522, C_523]: (k1_xboole_0=B_521 | k1_relset_1(A_522, B_521, C_523)=A_522 | ~v1_funct_2(C_523, A_522, B_521) | ~m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_522, B_521))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.94/2.15  tff(c_3395, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_3386])).
% 5.94/2.15  tff(c_3409, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3017, c_3395])).
% 5.94/2.15  tff(c_3410, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_3409])).
% 5.94/2.15  tff(c_20, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, A_10))=A_10 | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.94/2.15  tff(c_3428, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3410, c_20])).
% 5.94/2.15  tff(c_3434, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_3428])).
% 5.94/2.15  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.94/2.15  tff(c_3293, plain, (![A_514, B_515, C_516, D_517]: (k2_partfun1(A_514, B_515, C_516, D_517)=k7_relat_1(C_516, D_517) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))) | ~v1_funct_1(C_516))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.94/2.15  tff(c_3299, plain, (![D_517]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_517)=k7_relat_1('#skF_4', D_517) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_3293])).
% 5.94/2.15  tff(c_3312, plain, (![D_517]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_517)=k7_relat_1('#skF_4', D_517))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3299])).
% 5.94/2.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.94/2.15  tff(c_1031, plain, (![A_223, B_224, C_225]: (k1_relset_1(A_223, B_224, C_225)=k1_relat_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.94/2.15  tff(c_1041, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1031])).
% 5.94/2.15  tff(c_1377, plain, (![B_275, A_276, C_277]: (k1_xboole_0=B_275 | k1_relset_1(A_276, B_275, C_277)=A_276 | ~v1_funct_2(C_277, A_276, B_275) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_276, B_275))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.94/2.15  tff(c_1386, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1377])).
% 5.94/2.15  tff(c_1401, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1041, c_1386])).
% 5.94/2.15  tff(c_1402, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_70, c_1401])).
% 5.94/2.15  tff(c_1415, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1402, c_20])).
% 5.94/2.15  tff(c_1421, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1415])).
% 5.94/2.15  tff(c_1224, plain, (![A_261, B_262, C_263, D_264]: (k2_partfun1(A_261, B_262, C_263, D_264)=k7_relat_1(C_263, D_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_1(C_263))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.94/2.15  tff(c_1228, plain, (![D_264]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_264)=k7_relat_1('#skF_4', D_264) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1224])).
% 5.94/2.15  tff(c_1237, plain, (![D_264]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_264)=k7_relat_1('#skF_4', D_264))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1228])).
% 5.94/2.15  tff(c_1613, plain, (![A_293, B_294, C_295, D_296]: (m1_subset_1(k2_partfun1(A_293, B_294, C_295, D_296), k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~v1_funct_1(C_295))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.94/2.15  tff(c_1642, plain, (![D_264]: (m1_subset_1(k7_relat_1('#skF_4', D_264), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1237, c_1613])).
% 5.94/2.15  tff(c_1663, plain, (![D_297]: (m1_subset_1(k7_relat_1('#skF_4', D_297), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1642])).
% 5.94/2.15  tff(c_30, plain, (![D_24, B_22, C_23, A_21]: (m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(B_22, C_23))) | ~r1_tarski(k1_relat_1(D_24), B_22) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_21, C_23))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.94/2.15  tff(c_2430, plain, (![D_409, B_410]: (m1_subset_1(k7_relat_1('#skF_4', D_409), k1_zfmisc_1(k2_zfmisc_1(B_410, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_409)), B_410))), inference(resolution, [status(thm)], [c_1663, c_30])).
% 5.94/2.15  tff(c_274, plain, (![A_87, B_88, C_89, D_90]: (v1_funct_1(k2_partfun1(A_87, B_88, C_89, D_90)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.94/2.15  tff(c_276, plain, (![D_90]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_90)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_274])).
% 5.94/2.15  tff(c_283, plain, (![D_90]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_90)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_276])).
% 5.94/2.15  tff(c_52, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.94/2.15  tff(c_139, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.94/2.15  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_139])).
% 5.94/2.15  tff(c_287, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 5.94/2.15  tff(c_505, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_287])).
% 5.94/2.15  tff(c_1239, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_505])).
% 5.94/2.15  tff(c_2487, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_2430, c_1239])).
% 5.94/2.15  tff(c_2503, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1421, c_2487])).
% 5.94/2.15  tff(c_2506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_6, c_2503])).
% 5.94/2.15  tff(c_2508, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_287])).
% 5.94/2.15  tff(c_3016, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2508, c_3003])).
% 5.94/2.15  tff(c_3315, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3312, c_3312, c_3016])).
% 5.94/2.15  tff(c_2507, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_287])).
% 5.94/2.15  tff(c_3321, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3312, c_2507])).
% 5.94/2.15  tff(c_3320, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3312, c_2508])).
% 5.94/2.15  tff(c_3500, plain, (![B_528, C_529, A_530]: (k1_xboole_0=B_528 | v1_funct_2(C_529, A_530, B_528) | k1_relset_1(A_530, B_528, C_529)!=A_530 | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_530, B_528))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.94/2.15  tff(c_3506, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3320, c_3500])).
% 5.94/2.15  tff(c_3521, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3321, c_70, c_3506])).
% 5.94/2.15  tff(c_3748, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3315, c_3521])).
% 5.94/2.15  tff(c_3755, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3434, c_3748])).
% 5.94/2.15  tff(c_3759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3755])).
% 5.94/2.15  tff(c_3760, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_54])).
% 5.94/2.15  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.94/2.15  tff(c_3774, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_3760, c_14])).
% 5.94/2.15  tff(c_3761, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 5.94/2.15  tff(c_3767, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_3761])).
% 5.94/2.15  tff(c_3782, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3774, c_3767, c_58])).
% 5.94/2.15  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.94/2.15  tff(c_3783, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_3760, c_12])).
% 5.94/2.15  tff(c_3812, plain, (![C_554, A_555, B_556]: (v1_relat_1(C_554) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_555, B_556))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.94/2.15  tff(c_3859, plain, (![C_560]: (v1_relat_1(C_560) | ~m1_subset_1(C_560, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_3812])).
% 5.94/2.15  tff(c_3863, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3782, c_3859])).
% 5.94/2.15  tff(c_4352, plain, (![C_666, A_667, B_668]: (v4_relat_1(C_666, A_667) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.94/2.15  tff(c_4359, plain, (![C_669, A_670]: (v4_relat_1(C_669, A_670) | ~m1_subset_1(C_669, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_4352])).
% 5.94/2.15  tff(c_4363, plain, (![A_671]: (v4_relat_1('#skF_4', A_671))), inference(resolution, [status(thm)], [c_3782, c_4359])).
% 5.94/2.15  tff(c_16, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.94/2.15  tff(c_4366, plain, (![A_671]: (k7_relat_1('#skF_4', A_671)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4363, c_16])).
% 5.94/2.15  tff(c_4369, plain, (![A_671]: (k7_relat_1('#skF_4', A_671)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3863, c_4366])).
% 5.94/2.15  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.94/2.15  tff(c_3762, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_8])).
% 5.94/2.15  tff(c_4637, plain, (![B_719, A_720]: (k1_relat_1(k7_relat_1(B_719, A_720))=A_720 | ~r1_tarski(A_720, k1_relat_1(B_719)) | ~v1_relat_1(B_719))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.94/2.15  tff(c_5001, plain, (![B_779]: (k1_relat_1(k7_relat_1(B_779, '#skF_1'))='#skF_1' | ~v1_relat_1(B_779))), inference(resolution, [status(thm)], [c_3762, c_4637])).
% 5.94/2.15  tff(c_5014, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4369, c_5001])).
% 5.94/2.15  tff(c_5022, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3863, c_5014])).
% 5.94/2.15  tff(c_5136, plain, (![A_787, B_788, C_789]: (k1_relset_1(A_787, B_788, C_789)=k1_relat_1(C_789) | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(A_787, B_788))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.94/2.15  tff(c_5195, plain, (![B_797, C_798]: (k1_relset_1('#skF_1', B_797, C_798)=k1_relat_1(C_798) | ~m1_subset_1(C_798, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3774, c_5136])).
% 5.94/2.15  tff(c_5201, plain, (![B_797]: (k1_relset_1('#skF_1', B_797, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3782, c_5195])).
% 5.94/2.15  tff(c_5206, plain, (![B_797]: (k1_relset_1('#skF_1', B_797, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5022, c_5201])).
% 5.94/2.15  tff(c_38, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.94/2.15  tff(c_63, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 5.94/2.15  tff(c_5283, plain, (![C_802, B_803]: (v1_funct_2(C_802, '#skF_1', B_803) | k1_relset_1('#skF_1', B_803, C_802)!='#skF_1' | ~m1_subset_1(C_802, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3760, c_3760, c_3760, c_3760, c_63])).
% 5.94/2.15  tff(c_5289, plain, (![B_803]: (v1_funct_2('#skF_4', '#skF_1', B_803) | k1_relset_1('#skF_1', B_803, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_3782, c_5283])).
% 5.94/2.15  tff(c_5296, plain, (![B_803]: (v1_funct_2('#skF_4', '#skF_1', B_803))), inference(demodulation, [status(thm), theory('equality')], [c_5206, c_5289])).
% 5.94/2.15  tff(c_5403, plain, (![A_833, B_834, C_835, D_836]: (k2_partfun1(A_833, B_834, C_835, D_836)=k7_relat_1(C_835, D_836) | ~m1_subset_1(C_835, k1_zfmisc_1(k2_zfmisc_1(A_833, B_834))) | ~v1_funct_1(C_835))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.94/2.15  tff(c_5408, plain, (![A_837, C_838, D_839]: (k2_partfun1(A_837, '#skF_1', C_838, D_839)=k7_relat_1(C_838, D_839) | ~m1_subset_1(C_838, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_838))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_5403])).
% 5.94/2.15  tff(c_5414, plain, (![A_837, D_839]: (k2_partfun1(A_837, '#skF_1', '#skF_4', D_839)=k7_relat_1('#skF_4', D_839) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3782, c_5408])).
% 5.94/2.15  tff(c_5422, plain, (![A_837, D_839]: (k2_partfun1(A_837, '#skF_1', '#skF_4', D_839)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4369, c_5414])).
% 5.94/2.15  tff(c_4975, plain, (![A_772, B_773, C_774, D_775]: (k2_partfun1(A_772, B_773, C_774, D_775)=k7_relat_1(C_774, D_775) | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1(A_772, B_773))) | ~v1_funct_1(C_774))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.94/2.15  tff(c_4983, plain, (![A_776, C_777, D_778]: (k2_partfun1(A_776, '#skF_1', C_777, D_778)=k7_relat_1(C_777, D_778) | ~m1_subset_1(C_777, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_777))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_4975])).
% 5.94/2.15  tff(c_4987, plain, (![A_776, D_778]: (k2_partfun1(A_776, '#skF_1', '#skF_4', D_778)=k7_relat_1('#skF_4', D_778) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3782, c_4983])).
% 5.94/2.15  tff(c_4992, plain, (![A_776, D_778]: (k2_partfun1(A_776, '#skF_1', '#skF_4', D_778)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4369, c_4987])).
% 5.94/2.15  tff(c_4051, plain, (![A_594, B_595, C_596, D_597]: (v1_funct_1(k2_partfun1(A_594, B_595, C_596, D_597)) | ~m1_subset_1(C_596, k1_zfmisc_1(k2_zfmisc_1(A_594, B_595))) | ~v1_funct_1(C_596))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.94/2.15  tff(c_4056, plain, (![A_598, C_599, D_600]: (v1_funct_1(k2_partfun1(A_598, '#skF_1', C_599, D_600)) | ~m1_subset_1(C_599, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_599))), inference(superposition, [status(thm), theory('equality')], [c_3783, c_4051])).
% 5.94/2.15  tff(c_4058, plain, (![A_598, D_600]: (v1_funct_1(k2_partfun1(A_598, '#skF_1', '#skF_4', D_600)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3782, c_4056])).
% 5.94/2.15  tff(c_4061, plain, (![A_598, D_600]: (v1_funct_1(k2_partfun1(A_598, '#skF_1', '#skF_4', D_600)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4058])).
% 5.94/2.15  tff(c_3817, plain, (![B_557, A_558]: (B_557=A_558 | ~r1_tarski(B_557, A_558) | ~r1_tarski(A_558, B_557))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.94/2.15  tff(c_3825, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_3817])).
% 5.94/2.15  tff(c_3834, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3762, c_3825])).
% 5.94/2.15  tff(c_3864, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3834, c_3767, c_3834, c_3834, c_3767, c_3767, c_3834, c_3783, c_3767, c_3767, c_52])).
% 5.94/2.15  tff(c_3865, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3864])).
% 5.94/2.15  tff(c_4064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4061, c_3865])).
% 5.94/2.15  tff(c_4065, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3864])).
% 5.94/2.15  tff(c_4653, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4065])).
% 5.94/2.15  tff(c_4994, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4992, c_4653])).
% 5.94/2.15  tff(c_4998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3782, c_4994])).
% 5.94/2.15  tff(c_4999, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4065])).
% 5.94/2.15  tff(c_5434, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5422, c_4999])).
% 5.94/2.15  tff(c_5448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5296, c_5434])).
% 5.94/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.15  
% 5.94/2.15  Inference rules
% 5.94/2.15  ----------------------
% 5.94/2.15  #Ref     : 0
% 5.94/2.15  #Sup     : 1218
% 5.94/2.15  #Fact    : 0
% 5.94/2.15  #Define  : 0
% 5.94/2.15  #Split   : 31
% 5.94/2.15  #Chain   : 0
% 5.94/2.15  #Close   : 0
% 5.94/2.15  
% 5.94/2.15  Ordering : KBO
% 5.94/2.15  
% 5.94/2.15  Simplification rules
% 5.94/2.15  ----------------------
% 5.94/2.15  #Subsume      : 181
% 5.94/2.15  #Demod        : 926
% 5.94/2.15  #Tautology    : 591
% 5.94/2.15  #SimpNegUnit  : 44
% 5.94/2.15  #BackRed      : 49
% 5.94/2.15  
% 5.94/2.15  #Partial instantiations: 0
% 5.94/2.15  #Strategies tried      : 1
% 5.94/2.15  
% 5.94/2.15  Timing (in seconds)
% 5.94/2.15  ----------------------
% 5.94/2.15  Preprocessing        : 0.33
% 5.94/2.15  Parsing              : 0.17
% 5.94/2.15  CNF conversion       : 0.02
% 5.94/2.15  Main loop            : 1.04
% 5.94/2.15  Inferencing          : 0.38
% 5.94/2.15  Reduction            : 0.35
% 5.94/2.15  Demodulation         : 0.24
% 5.94/2.15  BG Simplification    : 0.04
% 5.94/2.16  Subsumption          : 0.17
% 5.94/2.16  Abstraction          : 0.04
% 5.94/2.16  MUC search           : 0.00
% 5.94/2.16  Cooper               : 0.00
% 5.94/2.16  Total                : 1.42
% 5.94/2.16  Index Insertion      : 0.00
% 5.94/2.16  Index Deletion       : 0.00
% 5.94/2.16  Index Matching       : 0.00
% 5.94/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
