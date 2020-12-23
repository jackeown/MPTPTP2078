%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 981 expanded)
%              Number of leaves         :   34 ( 315 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 (3191 expanded)
%              Number of equality atoms :   94 (1263 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_125,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_105,axiom,(
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

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_117,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_117])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1438,plain,(
    ! [A_248,B_249,C_250] :
      ( k1_relset_1(A_248,B_249,C_250) = k1_relat_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1452,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1438])).

tff(c_1654,plain,(
    ! [B_284,A_285,C_286] :
      ( k1_xboole_0 = B_284
      | k1_relset_1(A_285,B_284,C_286) = A_285
      | ~ v1_funct_2(C_286,A_285,B_284)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1663,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1654])).

tff(c_1677,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1452,c_1663])).

tff(c_1678,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1677])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k1_relat_1(k7_relat_1(B_9,A_8)) = A_8
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1699,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_18])).

tff(c_1705,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1699])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1569,plain,(
    ! [A_276,B_277,C_278,D_279] :
      ( k2_partfun1(A_276,B_277,C_278,D_279) = k7_relat_1(C_278,D_279)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277)))
      | ~ v1_funct_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1575,plain,(
    ! [D_279] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_279) = k7_relat_1('#skF_4',D_279)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_1569])).

tff(c_1588,plain,(
    ! [D_279] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_279) = k7_relat_1('#skF_4',D_279) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1575])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_292,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_282])).

tff(c_449,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_xboole_0 = B_136
      | k1_relset_1(A_137,B_136,C_138) = A_137
      | ~ v1_funct_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_455,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_449])).

tff(c_467,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_292,c_455])).

tff(c_468,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_467])).

tff(c_487,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_18])).

tff(c_493,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_487])).

tff(c_316,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k2_partfun1(A_112,B_113,C_114,D_115) = k7_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_318,plain,(
    ! [D_115] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_115) = k7_relat_1('#skF_4',D_115)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_316])).

tff(c_325,plain,(
    ! [D_115] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_115) = k7_relat_1('#skF_4',D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_318])).

tff(c_565,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( m1_subset_1(k2_partfun1(A_142,B_143,C_144,D_145),k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_592,plain,(
    ! [D_115] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_115),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_565])).

tff(c_612,plain,(
    ! [D_146] : m1_subset_1(k7_relat_1('#skF_4',D_146),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_592])).

tff(c_28,plain,(
    ! [D_22,B_20,C_21,A_19] :
      ( m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(B_20,C_21)))
      | ~ r1_tarski(k1_relat_1(D_22),B_20)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,C_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1315,plain,(
    ! [D_241,B_242] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_241),k1_zfmisc_1(k2_zfmisc_1(B_242,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_241)),B_242) ) ),
    inference(resolution,[status(thm)],[c_612,c_28])).

tff(c_206,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( v1_funct_1(k2_partfun1(A_70,B_71,C_72,D_73))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_208,plain,(
    ! [D_73] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_73))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_206])).

tff(c_215,plain,(
    ! [D_73] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_208])).

tff(c_48,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_128,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_128])).

tff(c_219,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_255,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_327,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_255])).

tff(c_1367,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1315,c_327])).

tff(c_1386,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_1367])).

tff(c_1391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_1386])).

tff(c_1393,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_1451,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1393,c_1438])).

tff(c_1592,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1588,c_1451])).

tff(c_1392,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_1598,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1392])).

tff(c_1597,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1393])).

tff(c_1802,plain,(
    ! [B_291,C_292,A_293] :
      ( k1_xboole_0 = B_291
      | v1_funct_2(C_292,A_293,B_291)
      | k1_relset_1(A_293,B_291,C_292) != A_293
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1808,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1597,c_1802])).

tff(c_1823,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1598,c_72,c_1808])).

tff(c_1854,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_1823])).

tff(c_1908,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_1854])).

tff(c_1912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1908])).

tff(c_1913,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1927,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1913,c_12])).

tff(c_1914,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1920,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1914])).

tff(c_1926,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_54])).

tff(c_1928,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1926])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1915,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1913,c_14])).

tff(c_2546,plain,(
    ! [A_430,B_431,C_432] :
      ( k1_relset_1(A_430,B_431,C_432) = k1_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2553,plain,(
    ! [B_433,C_434] :
      ( k1_relset_1('#skF_1',B_433,C_434) = k1_relat_1(C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_2546])).

tff(c_2559,plain,(
    ! [B_433] : k1_relset_1('#skF_1',B_433,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1928,c_2553])).

tff(c_34,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_59,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_2620,plain,(
    ! [C_443,B_444] :
      ( v1_funct_2(C_443,'#skF_1',B_444)
      | k1_relset_1('#skF_1',B_444,C_443) != '#skF_1'
      | ~ m1_subset_1(C_443,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1913,c_1913,c_1913,c_59])).

tff(c_2624,plain,(
    ! [B_444] :
      ( v1_funct_2('#skF_4','#skF_1',B_444)
      | k1_relset_1('#skF_1',B_444,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1928,c_2620])).

tff(c_2628,plain,(
    ! [B_444] :
      ( v1_funct_2('#skF_4','#skF_1',B_444)
      | k1_relat_1('#skF_4') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2559,c_2624])).

tff(c_2629,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2628])).

tff(c_1921,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_56])).

tff(c_38,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_60,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_2631,plain,(
    ! [B_445,C_446] :
      ( k1_relset_1('#skF_1',B_445,C_446) = '#skF_1'
      | ~ v1_funct_2(C_446,'#skF_1',B_445)
      | ~ m1_subset_1(C_446,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1913,c_1913,c_1913,c_60])).

tff(c_2633,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1921,c_2631])).

tff(c_2636,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_2559,c_2633])).

tff(c_2638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2629,c_2636])).

tff(c_2639,plain,(
    ! [B_444] : v1_funct_2('#skF_4','#skF_1',B_444) ),
    inference(splitRight,[status(thm)],[c_2628])).

tff(c_1963,plain,(
    ! [C_305,A_306,B_307] :
      ( v1_relat_1(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1974,plain,(
    ! [C_308] :
      ( v1_relat_1(C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_1963])).

tff(c_1978,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1928,c_1974])).

tff(c_2442,plain,(
    ! [C_417,A_418,B_419] :
      ( v4_relat_1(C_417,A_418)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_418,B_419))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2475,plain,(
    ! [C_421,A_422] :
      ( v4_relat_1(C_421,A_422)
      | ~ m1_subset_1(C_421,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1927,c_2442])).

tff(c_2483,plain,(
    ! [A_423] : v4_relat_1('#skF_4',A_423) ),
    inference(resolution,[status(thm)],[c_1928,c_2475])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2486,plain,(
    ! [A_423] :
      ( k7_relat_1('#skF_4',A_423) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2483,c_16])).

tff(c_2489,plain,(
    ! [A_423] : k7_relat_1('#skF_4',A_423) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_2486])).

tff(c_2714,plain,(
    ! [A_463,B_464,C_465,D_466] :
      ( k2_partfun1(A_463,B_464,C_465,D_466) = k7_relat_1(C_465,D_466)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))
      | ~ v1_funct_1(C_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2747,plain,(
    ! [A_475,C_476,D_477] :
      ( k2_partfun1(A_475,'#skF_1',C_476,D_477) = k7_relat_1(C_476,D_477)
      | ~ m1_subset_1(C_476,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_476) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1927,c_2714])).

tff(c_2751,plain,(
    ! [A_475,D_477] :
      ( k2_partfun1(A_475,'#skF_1','#skF_4',D_477) = k7_relat_1('#skF_4',D_477)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1928,c_2747])).

tff(c_2757,plain,(
    ! [A_475,D_477] : k2_partfun1(A_475,'#skF_1','#skF_4',D_477) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2489,c_2751])).

tff(c_2216,plain,(
    ! [C_366,A_367,B_368] :
      ( v4_relat_1(C_366,A_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_367,B_368))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2246,plain,(
    ! [C_372,A_373] :
      ( v4_relat_1(C_372,A_373)
      | ~ m1_subset_1(C_372,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1927,c_2216])).

tff(c_2251,plain,(
    ! [A_374] : v4_relat_1('#skF_4',A_374) ),
    inference(resolution,[status(thm)],[c_1928,c_2246])).

tff(c_2254,plain,(
    ! [A_374] :
      ( k7_relat_1('#skF_4',A_374) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2251,c_16])).

tff(c_2257,plain,(
    ! [A_374] : k7_relat_1('#skF_4',A_374) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_2254])).

tff(c_2415,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k2_partfun1(A_404,B_405,C_406,D_407) = k7_relat_1(C_406,D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405)))
      | ~ v1_funct_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2427,plain,(
    ! [B_413,C_414,D_415] :
      ( k2_partfun1('#skF_1',B_413,C_414,D_415) = k7_relat_1(C_414,D_415)
      | ~ m1_subset_1(C_414,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_2415])).

tff(c_2429,plain,(
    ! [B_413,D_415] :
      ( k2_partfun1('#skF_1',B_413,'#skF_4',D_415) = k7_relat_1('#skF_4',D_415)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1928,c_2427])).

tff(c_2432,plain,(
    ! [B_413,D_415] : k2_partfun1('#skF_1',B_413,'#skF_4',D_415) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2257,c_2429])).

tff(c_2167,plain,(
    ! [A_347,B_348,C_349,D_350] :
      ( v1_funct_1(k2_partfun1(A_347,B_348,C_349,D_350))
      | ~ m1_subset_1(C_349,k1_zfmisc_1(k2_zfmisc_1(A_347,B_348)))
      | ~ v1_funct_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2172,plain,(
    ! [B_351,C_352,D_353] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_351,C_352,D_353))
      | ~ m1_subset_1(C_352,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1915,c_2167])).

tff(c_2174,plain,(
    ! [B_351,D_353] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_351,'#skF_4',D_353))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1928,c_2172])).

tff(c_2177,plain,(
    ! [B_351,D_353] : v1_funct_1(k2_partfun1('#skF_1',B_351,'#skF_4',D_353)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2174])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1952,plain,(
    ! [A_304] :
      ( A_304 = '#skF_1'
      | ~ r1_tarski(A_304,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1913,c_1913,c_8])).

tff(c_1962,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_1952])).

tff(c_1979,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_1920,c_1962,c_1962,c_1920,c_1920,c_1962,c_1927,c_1920,c_1920,c_48])).

tff(c_1980,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1979])).

tff(c_2180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2177,c_1980])).

tff(c_2181,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1979])).

tff(c_2214,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2181])).

tff(c_2434,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2432,c_2214])).

tff(c_2438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_2434])).

tff(c_2439,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2181])).

tff(c_2765,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2757,c_2439])).

tff(c_2778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2639,c_2765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:53:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.82  
% 4.54/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.54/1.82  
% 4.54/1.82  %Foreground sorts:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Background operators:
% 4.54/1.82  
% 4.54/1.82  
% 4.54/1.82  %Foreground operators:
% 4.54/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.54/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.54/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.54/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.54/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.54/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.82  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.54/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.54/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.82  
% 4.68/1.85  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 4.68/1.85  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.68/1.85  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.68/1.85  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.68/1.85  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 4.68/1.85  tff(f_105, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.68/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.68/1.85  tff(f_99, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.68/1.85  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.68/1.85  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.68/1.85  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.68/1.85  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.68/1.85  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.68/1.85  tff(c_52, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.68/1.85  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.68/1.85  tff(c_117, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.68/1.85  tff(c_125, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_117])).
% 4.68/1.85  tff(c_50, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.68/1.85  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 4.68/1.85  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.68/1.85  tff(c_1438, plain, (![A_248, B_249, C_250]: (k1_relset_1(A_248, B_249, C_250)=k1_relat_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.68/1.85  tff(c_1452, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1438])).
% 4.68/1.85  tff(c_1654, plain, (![B_284, A_285, C_286]: (k1_xboole_0=B_284 | k1_relset_1(A_285, B_284, C_286)=A_285 | ~v1_funct_2(C_286, A_285, B_284) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.85  tff(c_1663, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_1654])).
% 4.68/1.85  tff(c_1677, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1452, c_1663])).
% 4.68/1.85  tff(c_1678, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_1677])).
% 4.68/1.85  tff(c_18, plain, (![B_9, A_8]: (k1_relat_1(k7_relat_1(B_9, A_8))=A_8 | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.68/1.85  tff(c_1699, plain, (![A_8]: (k1_relat_1(k7_relat_1('#skF_4', A_8))=A_8 | ~r1_tarski(A_8, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_18])).
% 4.68/1.85  tff(c_1705, plain, (![A_8]: (k1_relat_1(k7_relat_1('#skF_4', A_8))=A_8 | ~r1_tarski(A_8, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1699])).
% 4.68/1.85  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.68/1.85  tff(c_1569, plain, (![A_276, B_277, C_278, D_279]: (k2_partfun1(A_276, B_277, C_278, D_279)=k7_relat_1(C_278, D_279) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))) | ~v1_funct_1(C_278))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.68/1.85  tff(c_1575, plain, (![D_279]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_279)=k7_relat_1('#skF_4', D_279) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_1569])).
% 4.68/1.85  tff(c_1588, plain, (![D_279]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_279)=k7_relat_1('#skF_4', D_279))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1575])).
% 4.68/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.85  tff(c_282, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.68/1.85  tff(c_292, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_282])).
% 4.68/1.85  tff(c_449, plain, (![B_136, A_137, C_138]: (k1_xboole_0=B_136 | k1_relset_1(A_137, B_136, C_138)=A_137 | ~v1_funct_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.85  tff(c_455, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_449])).
% 4.68/1.85  tff(c_467, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_292, c_455])).
% 4.68/1.85  tff(c_468, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_467])).
% 4.68/1.85  tff(c_487, plain, (![A_8]: (k1_relat_1(k7_relat_1('#skF_4', A_8))=A_8 | ~r1_tarski(A_8, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_468, c_18])).
% 4.68/1.85  tff(c_493, plain, (![A_8]: (k1_relat_1(k7_relat_1('#skF_4', A_8))=A_8 | ~r1_tarski(A_8, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_487])).
% 4.68/1.85  tff(c_316, plain, (![A_112, B_113, C_114, D_115]: (k2_partfun1(A_112, B_113, C_114, D_115)=k7_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.68/1.85  tff(c_318, plain, (![D_115]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_115)=k7_relat_1('#skF_4', D_115) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_316])).
% 4.68/1.85  tff(c_325, plain, (![D_115]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_115)=k7_relat_1('#skF_4', D_115))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_318])).
% 4.68/1.85  tff(c_565, plain, (![A_142, B_143, C_144, D_145]: (m1_subset_1(k2_partfun1(A_142, B_143, C_144, D_145), k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.68/1.85  tff(c_592, plain, (![D_115]: (m1_subset_1(k7_relat_1('#skF_4', D_115), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_325, c_565])).
% 4.68/1.85  tff(c_612, plain, (![D_146]: (m1_subset_1(k7_relat_1('#skF_4', D_146), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_592])).
% 4.68/1.85  tff(c_28, plain, (![D_22, B_20, C_21, A_19]: (m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(B_20, C_21))) | ~r1_tarski(k1_relat_1(D_22), B_20) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, C_21))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/1.85  tff(c_1315, plain, (![D_241, B_242]: (m1_subset_1(k7_relat_1('#skF_4', D_241), k1_zfmisc_1(k2_zfmisc_1(B_242, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_241)), B_242))), inference(resolution, [status(thm)], [c_612, c_28])).
% 4.68/1.85  tff(c_206, plain, (![A_70, B_71, C_72, D_73]: (v1_funct_1(k2_partfun1(A_70, B_71, C_72, D_73)) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.68/1.85  tff(c_208, plain, (![D_73]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_73)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_206])).
% 4.68/1.85  tff(c_215, plain, (![D_73]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_73)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_208])).
% 4.68/1.85  tff(c_48, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.68/1.85  tff(c_128, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.68/1.85  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_128])).
% 4.68/1.85  tff(c_219, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_48])).
% 4.68/1.85  tff(c_255, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_219])).
% 4.68/1.85  tff(c_327, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_255])).
% 4.68/1.85  tff(c_1367, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_1315, c_327])).
% 4.68/1.85  tff(c_1386, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_493, c_1367])).
% 4.68/1.85  tff(c_1391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_1386])).
% 4.68/1.85  tff(c_1393, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_219])).
% 4.68/1.85  tff(c_1451, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1393, c_1438])).
% 4.68/1.85  tff(c_1592, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1588, c_1451])).
% 4.68/1.85  tff(c_1392, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_219])).
% 4.68/1.85  tff(c_1598, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1392])).
% 4.68/1.85  tff(c_1597, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1393])).
% 4.68/1.85  tff(c_1802, plain, (![B_291, C_292, A_293]: (k1_xboole_0=B_291 | v1_funct_2(C_292, A_293, B_291) | k1_relset_1(A_293, B_291, C_292)!=A_293 | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_291))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.85  tff(c_1808, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1597, c_1802])).
% 4.68/1.85  tff(c_1823, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1598, c_72, c_1808])).
% 4.68/1.85  tff(c_1854, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1592, c_1823])).
% 4.68/1.85  tff(c_1908, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1705, c_1854])).
% 4.68/1.85  tff(c_1912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1908])).
% 4.68/1.85  tff(c_1913, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_50])).
% 4.68/1.85  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.68/1.85  tff(c_1927, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1913, c_12])).
% 4.68/1.85  tff(c_1914, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 4.68/1.85  tff(c_1920, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1914])).
% 4.68/1.85  tff(c_1926, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_54])).
% 4.68/1.85  tff(c_1928, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1926])).
% 4.68/1.85  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.68/1.85  tff(c_1915, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1913, c_14])).
% 4.68/1.85  tff(c_2546, plain, (![A_430, B_431, C_432]: (k1_relset_1(A_430, B_431, C_432)=k1_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.68/1.85  tff(c_2553, plain, (![B_433, C_434]: (k1_relset_1('#skF_1', B_433, C_434)=k1_relat_1(C_434) | ~m1_subset_1(C_434, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_2546])).
% 4.68/1.85  tff(c_2559, plain, (![B_433]: (k1_relset_1('#skF_1', B_433, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1928, c_2553])).
% 4.68/1.85  tff(c_34, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.85  tff(c_59, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 4.68/1.85  tff(c_2620, plain, (![C_443, B_444]: (v1_funct_2(C_443, '#skF_1', B_444) | k1_relset_1('#skF_1', B_444, C_443)!='#skF_1' | ~m1_subset_1(C_443, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1913, c_1913, c_1913, c_59])).
% 4.68/1.85  tff(c_2624, plain, (![B_444]: (v1_funct_2('#skF_4', '#skF_1', B_444) | k1_relset_1('#skF_1', B_444, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_1928, c_2620])).
% 4.68/1.85  tff(c_2628, plain, (![B_444]: (v1_funct_2('#skF_4', '#skF_1', B_444) | k1_relat_1('#skF_4')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2559, c_2624])).
% 4.68/1.85  tff(c_2629, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2628])).
% 4.68/1.85  tff(c_1921, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_56])).
% 4.68/1.85  tff(c_38, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.68/1.85  tff(c_60, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 4.68/1.85  tff(c_2631, plain, (![B_445, C_446]: (k1_relset_1('#skF_1', B_445, C_446)='#skF_1' | ~v1_funct_2(C_446, '#skF_1', B_445) | ~m1_subset_1(C_446, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1913, c_1913, c_1913, c_60])).
% 4.68/1.85  tff(c_2633, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_1921, c_2631])).
% 4.68/1.85  tff(c_2636, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_2559, c_2633])).
% 4.68/1.85  tff(c_2638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2629, c_2636])).
% 4.68/1.85  tff(c_2639, plain, (![B_444]: (v1_funct_2('#skF_4', '#skF_1', B_444))), inference(splitRight, [status(thm)], [c_2628])).
% 4.68/1.85  tff(c_1963, plain, (![C_305, A_306, B_307]: (v1_relat_1(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.68/1.85  tff(c_1974, plain, (![C_308]: (v1_relat_1(C_308) | ~m1_subset_1(C_308, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_1963])).
% 4.68/1.85  tff(c_1978, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1928, c_1974])).
% 4.68/1.85  tff(c_2442, plain, (![C_417, A_418, B_419]: (v4_relat_1(C_417, A_418) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_418, B_419))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.68/1.85  tff(c_2475, plain, (![C_421, A_422]: (v4_relat_1(C_421, A_422) | ~m1_subset_1(C_421, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1927, c_2442])).
% 4.68/1.85  tff(c_2483, plain, (![A_423]: (v4_relat_1('#skF_4', A_423))), inference(resolution, [status(thm)], [c_1928, c_2475])).
% 4.68/1.85  tff(c_16, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.68/1.85  tff(c_2486, plain, (![A_423]: (k7_relat_1('#skF_4', A_423)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2483, c_16])).
% 4.68/1.85  tff(c_2489, plain, (![A_423]: (k7_relat_1('#skF_4', A_423)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_2486])).
% 4.68/1.85  tff(c_2714, plain, (![A_463, B_464, C_465, D_466]: (k2_partfun1(A_463, B_464, C_465, D_466)=k7_relat_1(C_465, D_466) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))) | ~v1_funct_1(C_465))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.68/1.85  tff(c_2747, plain, (![A_475, C_476, D_477]: (k2_partfun1(A_475, '#skF_1', C_476, D_477)=k7_relat_1(C_476, D_477) | ~m1_subset_1(C_476, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_476))), inference(superposition, [status(thm), theory('equality')], [c_1927, c_2714])).
% 4.68/1.85  tff(c_2751, plain, (![A_475, D_477]: (k2_partfun1(A_475, '#skF_1', '#skF_4', D_477)=k7_relat_1('#skF_4', D_477) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1928, c_2747])).
% 4.68/1.85  tff(c_2757, plain, (![A_475, D_477]: (k2_partfun1(A_475, '#skF_1', '#skF_4', D_477)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2489, c_2751])).
% 4.68/1.85  tff(c_2216, plain, (![C_366, A_367, B_368]: (v4_relat_1(C_366, A_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_367, B_368))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.68/1.85  tff(c_2246, plain, (![C_372, A_373]: (v4_relat_1(C_372, A_373) | ~m1_subset_1(C_372, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1927, c_2216])).
% 4.68/1.85  tff(c_2251, plain, (![A_374]: (v4_relat_1('#skF_4', A_374))), inference(resolution, [status(thm)], [c_1928, c_2246])).
% 4.68/1.85  tff(c_2254, plain, (![A_374]: (k7_relat_1('#skF_4', A_374)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2251, c_16])).
% 4.68/1.85  tff(c_2257, plain, (![A_374]: (k7_relat_1('#skF_4', A_374)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_2254])).
% 4.68/1.85  tff(c_2415, plain, (![A_404, B_405, C_406, D_407]: (k2_partfun1(A_404, B_405, C_406, D_407)=k7_relat_1(C_406, D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))) | ~v1_funct_1(C_406))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.68/1.85  tff(c_2427, plain, (![B_413, C_414, D_415]: (k2_partfun1('#skF_1', B_413, C_414, D_415)=k7_relat_1(C_414, D_415) | ~m1_subset_1(C_414, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_414))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_2415])).
% 4.68/1.85  tff(c_2429, plain, (![B_413, D_415]: (k2_partfun1('#skF_1', B_413, '#skF_4', D_415)=k7_relat_1('#skF_4', D_415) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1928, c_2427])).
% 4.68/1.85  tff(c_2432, plain, (![B_413, D_415]: (k2_partfun1('#skF_1', B_413, '#skF_4', D_415)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2257, c_2429])).
% 4.68/1.85  tff(c_2167, plain, (![A_347, B_348, C_349, D_350]: (v1_funct_1(k2_partfun1(A_347, B_348, C_349, D_350)) | ~m1_subset_1(C_349, k1_zfmisc_1(k2_zfmisc_1(A_347, B_348))) | ~v1_funct_1(C_349))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.68/1.85  tff(c_2172, plain, (![B_351, C_352, D_353]: (v1_funct_1(k2_partfun1('#skF_1', B_351, C_352, D_353)) | ~m1_subset_1(C_352, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_352))), inference(superposition, [status(thm), theory('equality')], [c_1915, c_2167])).
% 4.68/1.85  tff(c_2174, plain, (![B_351, D_353]: (v1_funct_1(k2_partfun1('#skF_1', B_351, '#skF_4', D_353)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1928, c_2172])).
% 4.68/1.85  tff(c_2177, plain, (![B_351, D_353]: (v1_funct_1(k2_partfun1('#skF_1', B_351, '#skF_4', D_353)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2174])).
% 4.68/1.85  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.85  tff(c_1952, plain, (![A_304]: (A_304='#skF_1' | ~r1_tarski(A_304, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1913, c_1913, c_8])).
% 4.68/1.85  tff(c_1962, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_52, c_1952])).
% 4.68/1.85  tff(c_1979, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1962, c_1920, c_1962, c_1962, c_1920, c_1920, c_1962, c_1927, c_1920, c_1920, c_48])).
% 4.68/1.85  tff(c_1980, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1979])).
% 4.68/1.85  tff(c_2180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2177, c_1980])).
% 4.68/1.85  tff(c_2181, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1979])).
% 4.68/1.85  tff(c_2214, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2181])).
% 4.68/1.85  tff(c_2434, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2432, c_2214])).
% 4.68/1.85  tff(c_2438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1928, c_2434])).
% 4.68/1.85  tff(c_2439, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2181])).
% 4.68/1.85  tff(c_2765, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2757, c_2439])).
% 4.68/1.85  tff(c_2778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2639, c_2765])).
% 4.68/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.85  
% 4.68/1.85  Inference rules
% 4.68/1.85  ----------------------
% 4.68/1.85  #Ref     : 0
% 4.68/1.85  #Sup     : 608
% 4.68/1.85  #Fact    : 0
% 4.68/1.85  #Define  : 0
% 4.68/1.85  #Split   : 17
% 4.68/1.85  #Chain   : 0
% 4.68/1.85  #Close   : 0
% 4.68/1.85  
% 4.68/1.85  Ordering : KBO
% 4.68/1.85  
% 4.68/1.85  Simplification rules
% 4.68/1.85  ----------------------
% 4.68/1.85  #Subsume      : 57
% 4.68/1.85  #Demod        : 483
% 4.68/1.85  #Tautology    : 294
% 4.68/1.85  #SimpNegUnit  : 20
% 4.68/1.85  #BackRed      : 57
% 4.68/1.85  
% 4.68/1.85  #Partial instantiations: 0
% 4.68/1.85  #Strategies tried      : 1
% 4.68/1.85  
% 4.68/1.85  Timing (in seconds)
% 4.68/1.85  ----------------------
% 4.68/1.85  Preprocessing        : 0.33
% 4.68/1.85  Parsing              : 0.18
% 4.68/1.85  CNF conversion       : 0.02
% 4.68/1.85  Main loop            : 0.71
% 4.68/1.85  Inferencing          : 0.25
% 4.68/1.85  Reduction            : 0.24
% 4.68/1.85  Demodulation         : 0.17
% 4.68/1.85  BG Simplification    : 0.03
% 4.68/1.85  Subsumption          : 0.12
% 4.68/1.85  Abstraction          : 0.03
% 4.68/1.85  MUC search           : 0.00
% 4.68/1.85  Cooper               : 0.00
% 4.68/1.85  Total                : 1.09
% 4.68/1.85  Index Insertion      : 0.00
% 4.68/1.85  Index Deletion       : 0.00
% 4.68/1.85  Index Matching       : 0.00
% 4.68/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
