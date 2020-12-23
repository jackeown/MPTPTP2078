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
% DateTime   : Thu Dec  3 10:13:40 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 907 expanded)
%              Number of leaves         :   35 ( 297 expanded)
%              Depth                    :   10
%              Number of atoms          :  280 (2957 expanded)
%              Number of equality atoms :   97 (1153 expanded)
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

tff(f_140,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_120,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_82,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
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

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_140,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_143,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_143])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1602,plain,(
    ! [A_298,B_299,C_300] :
      ( k1_relset_1(A_298,B_299,C_300) = k1_relat_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1616,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1602])).

tff(c_1923,plain,(
    ! [B_351,A_352,C_353] :
      ( k1_xboole_0 = B_351
      | k1_relset_1(A_352,B_351,C_353) = A_352
      | ~ v1_funct_2(C_353,A_352,B_351)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1935,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1923])).

tff(c_1947,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1616,c_1935])).

tff(c_1948,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1947])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1970,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1948,c_24])).

tff(c_2048,plain,(
    ! [A_357] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_357)) = A_357
      | ~ r1_tarski(A_357,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_1970])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1695,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( k2_partfun1(A_329,B_330,C_331,D_332) = k7_relat_1(C_331,D_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1701,plain,(
    ! [D_332] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_332) = k7_relat_1('#skF_4',D_332)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_1695])).

tff(c_1709,plain,(
    ! [D_332] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_332) = k7_relat_1('#skF_4',D_332) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1701])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_383,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_393,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_383])).

tff(c_606,plain,(
    ! [B_170,A_171,C_172] :
      ( k1_xboole_0 = B_170
      | k1_relset_1(A_171,B_170,C_172) = A_171
      | ~ v1_funct_2(C_172,A_171,B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_615,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_606])).

tff(c_624,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_393,c_615])).

tff(c_625,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_624])).

tff(c_644,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_24])).

tff(c_650,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_644])).

tff(c_482,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k2_partfun1(A_149,B_150,C_151,D_152) = k7_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_486,plain,(
    ! [D_152] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_152) = k7_relat_1('#skF_4',D_152)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_482])).

tff(c_491,plain,(
    ! [D_152] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_152) = k7_relat_1('#skF_4',D_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_486])).

tff(c_806,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( m1_subset_1(k2_partfun1(A_187,B_188,C_189,D_190),k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_833,plain,(
    ! [D_152] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_152),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_806])).

tff(c_855,plain,(
    ! [D_191] : m1_subset_1(k7_relat_1('#skF_4',D_191),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_833])).

tff(c_32,plain,(
    ! [D_26,B_24,C_25,A_23] :
      ( m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(B_24,C_25)))
      | ~ r1_tarski(k1_relat_1(D_26),B_24)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_23,C_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1395,plain,(
    ! [D_275,B_276] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_275),k1_zfmisc_1(k2_zfmisc_1(B_276,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_275)),B_276) ) ),
    inference(resolution,[status(thm)],[c_855,c_32])).

tff(c_268,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( v1_funct_1(k2_partfun1(A_87,B_88,C_89,D_90))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_272,plain,(
    ! [D_90] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_90))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_268])).

tff(c_277,plain,(
    ! [D_90] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_272])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_148,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_148])).

tff(c_291,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_304,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_493,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_304])).

tff(c_1447,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1395,c_493])).

tff(c_1473,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_1447])).

tff(c_1476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6,c_1473])).

tff(c_1478,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_1615,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1478,c_1602])).

tff(c_1712,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1709,c_1615])).

tff(c_1477,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_1718,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1477])).

tff(c_1717,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_1478])).

tff(c_1870,plain,(
    ! [B_342,C_343,A_344] :
      ( k1_xboole_0 = B_342
      | v1_funct_2(C_343,A_344,B_342)
      | k1_relset_1(A_344,B_342,C_343) != A_344
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_344,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1876,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1717,c_1870])).

tff(c_1891,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1718,c_71,c_1876])).

tff(c_1896,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1712,c_1891])).

tff(c_2054,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2048,c_1896])).

tff(c_2079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2054])).

tff(c_2080,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2093,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_14])).

tff(c_2081,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2086,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2081])).

tff(c_2103,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2093,c_2086,c_60])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2104,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_12])).

tff(c_2833,plain,(
    ! [A_503,B_504,C_505] :
      ( k1_relset_1(A_503,B_504,C_505) = k1_relat_1(C_505)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_503,B_504))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2840,plain,(
    ! [A_506,C_507] :
      ( k1_relset_1(A_506,'#skF_1',C_507) = k1_relat_1(C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2833])).

tff(c_2858,plain,(
    ! [A_510] : k1_relset_1(A_510,'#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2103,c_2840])).

tff(c_2087,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_62])).

tff(c_44,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_65,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_2848,plain,(
    ! [B_508,C_509] :
      ( k1_relset_1('#skF_1',B_508,C_509) = '#skF_1'
      | ~ v1_funct_2(C_509,'#skF_1',B_508)
      | ~ m1_subset_1(C_509,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_2080,c_2080,c_65])).

tff(c_2850,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2087,c_2848])).

tff(c_2853,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2850])).

tff(c_2862,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2858,c_2853])).

tff(c_2893,plain,(
    ! [B_512,C_513] :
      ( k1_relset_1('#skF_1',B_512,C_513) = k1_relat_1(C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2093,c_2833])).

tff(c_2897,plain,(
    ! [B_512] : k1_relset_1('#skF_1',B_512,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2103,c_2893])).

tff(c_2900,plain,(
    ! [B_512] : k1_relset_1('#skF_1',B_512,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2862,c_2897])).

tff(c_40,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_2917,plain,(
    ! [C_515,B_516] :
      ( v1_funct_2(C_515,'#skF_1',B_516)
      | k1_relset_1('#skF_1',B_516,C_515) != '#skF_1'
      | ~ m1_subset_1(C_515,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_2080,c_2080,c_66])).

tff(c_2921,plain,(
    ! [B_516] :
      ( v1_funct_2('#skF_4','#skF_1',B_516)
      | k1_relset_1('#skF_1',B_516,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2103,c_2917])).

tff(c_2925,plain,(
    ! [B_516] : v1_funct_2('#skF_4','#skF_1',B_516) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_2921])).

tff(c_2094,plain,(
    ! [B_360] : k2_zfmisc_1('#skF_1',B_360) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_14])).

tff(c_2098,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2094,c_18])).

tff(c_2161,plain,(
    ! [B_366,A_367] :
      ( v1_relat_1(B_366)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(A_367))
      | ~ v1_relat_1(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2164,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2103,c_2161])).

tff(c_2167,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_2164])).

tff(c_2693,plain,(
    ! [C_485,A_486,B_487] :
      ( v4_relat_1(C_485,A_486)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_486,B_487))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2702,plain,(
    ! [C_489,A_490] :
      ( v4_relat_1(C_489,A_490)
      | ~ m1_subset_1(C_489,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2693])).

tff(c_2706,plain,(
    ! [A_491] : v4_relat_1('#skF_4',A_491) ),
    inference(resolution,[status(thm)],[c_2103,c_2702])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2709,plain,(
    ! [A_491] :
      ( k7_relat_1('#skF_4',A_491) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2706,c_20])).

tff(c_2712,plain,(
    ! [A_491] : k7_relat_1('#skF_4',A_491) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2709])).

tff(c_3001,plain,(
    ! [A_542,B_543,C_544,D_545] :
      ( k2_partfun1(A_542,B_543,C_544,D_545) = k7_relat_1(C_544,D_545)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(A_542,B_543)))
      | ~ v1_funct_1(C_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3006,plain,(
    ! [A_546,C_547,D_548] :
      ( k2_partfun1(A_546,'#skF_1',C_547,D_548) = k7_relat_1(C_547,D_548)
      | ~ m1_subset_1(C_547,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_547) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_3001])).

tff(c_3010,plain,(
    ! [A_546,D_548] :
      ( k2_partfun1(A_546,'#skF_1','#skF_4',D_548) = k7_relat_1('#skF_4',D_548)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2103,c_3006])).

tff(c_3016,plain,(
    ! [A_546,D_548] : k2_partfun1(A_546,'#skF_1','#skF_4',D_548) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2712,c_3010])).

tff(c_2445,plain,(
    ! [C_428,A_429,B_430] :
      ( v4_relat_1(C_428,A_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2452,plain,(
    ! [C_431,A_432] :
      ( v4_relat_1(C_431,A_432)
      | ~ m1_subset_1(C_431,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2445])).

tff(c_2458,plain,(
    ! [A_433] : v4_relat_1('#skF_4',A_433) ),
    inference(resolution,[status(thm)],[c_2103,c_2452])).

tff(c_2461,plain,(
    ! [A_433] :
      ( k7_relat_1('#skF_4',A_433) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2458,c_20])).

tff(c_2464,plain,(
    ! [A_433] : k7_relat_1('#skF_4',A_433) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2461])).

tff(c_2670,plain,(
    ! [A_476,B_477,C_478,D_479] :
      ( k2_partfun1(A_476,B_477,C_478,D_479) = k7_relat_1(C_478,D_479)
      | ~ m1_subset_1(C_478,k1_zfmisc_1(k2_zfmisc_1(A_476,B_477)))
      | ~ v1_funct_1(C_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2675,plain,(
    ! [A_480,C_481,D_482] :
      ( k2_partfun1(A_480,'#skF_1',C_481,D_482) = k7_relat_1(C_481,D_482)
      | ~ m1_subset_1(C_481,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2670])).

tff(c_2677,plain,(
    ! [A_480,D_482] :
      ( k2_partfun1(A_480,'#skF_1','#skF_4',D_482) = k7_relat_1('#skF_4',D_482)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2103,c_2675])).

tff(c_2680,plain,(
    ! [A_480,D_482] : k2_partfun1(A_480,'#skF_1','#skF_4',D_482) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2464,c_2677])).

tff(c_2387,plain,(
    ! [A_408,B_409,C_410,D_411] :
      ( v1_funct_1(k2_partfun1(A_408,B_409,C_410,D_411))
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_408,B_409)))
      | ~ v1_funct_1(C_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2392,plain,(
    ! [A_412,C_413,D_414] :
      ( v1_funct_1(k2_partfun1(A_412,'#skF_1',C_413,D_414))
      | ~ m1_subset_1(C_413,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_413) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_2387])).

tff(c_2394,plain,(
    ! [A_412,D_414] :
      ( v1_funct_1(k2_partfun1(A_412,'#skF_1','#skF_4',D_414))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2103,c_2392])).

tff(c_2397,plain,(
    ! [A_412,D_414] : v1_funct_1(k2_partfun1(A_412,'#skF_1','#skF_4',D_414)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2394])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2124,plain,(
    ! [A_362] :
      ( A_362 = '#skF_1'
      | ~ r1_tarski(A_362,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_2080,c_8])).

tff(c_2134,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_2124])).

tff(c_2168,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2134,c_2086,c_2134,c_2134,c_2086,c_2086,c_2134,c_2104,c_2086,c_2086,c_54])).

tff(c_2169,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2168])).

tff(c_2400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2397,c_2169])).

tff(c_2401,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2168])).

tff(c_2438,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2401])).

tff(c_2682,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2680,c_2438])).

tff(c_2686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2103,c_2682])).

tff(c_2687,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2401])).

tff(c_3023,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3016,c_2687])).

tff(c_3036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2925,c_3023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.00  
% 5.25/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.01  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.25/2.01  
% 5.25/2.01  %Foreground sorts:
% 5.25/2.01  
% 5.25/2.01  
% 5.25/2.01  %Background operators:
% 5.25/2.01  
% 5.25/2.01  
% 5.25/2.01  %Foreground operators:
% 5.25/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.25/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.25/2.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.25/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.25/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.25/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.25/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.25/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.25/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.25/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.25/2.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.25/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.25/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.25/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.25/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.25/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.25/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.25/2.01  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.25/2.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.25/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.25/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.25/2.01  
% 5.25/2.03  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 5.25/2.03  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.25/2.03  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.25/2.03  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.25/2.03  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.25/2.03  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 5.25/2.03  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.25/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.25/2.03  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.25/2.03  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.25/2.03  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.25/2.03  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.25/2.03  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.25/2.03  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.25/2.03  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.25/2.03  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.25/2.03  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.25/2.03  tff(c_140, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.25/2.03  tff(c_143, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_140])).
% 5.25/2.03  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_143])).
% 5.25/2.03  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.25/2.03  tff(c_71, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 5.25/2.03  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.25/2.03  tff(c_1602, plain, (![A_298, B_299, C_300]: (k1_relset_1(A_298, B_299, C_300)=k1_relat_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.25/2.03  tff(c_1616, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1602])).
% 5.25/2.03  tff(c_1923, plain, (![B_351, A_352, C_353]: (k1_xboole_0=B_351 | k1_relset_1(A_352, B_351, C_353)=A_352 | ~v1_funct_2(C_353, A_352, B_351) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_352, B_351))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.03  tff(c_1935, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1923])).
% 5.25/2.03  tff(c_1947, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1616, c_1935])).
% 5.25/2.03  tff(c_1948, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_1947])).
% 5.25/2.03  tff(c_24, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.25/2.03  tff(c_1970, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1948, c_24])).
% 5.25/2.03  tff(c_2048, plain, (![A_357]: (k1_relat_1(k7_relat_1('#skF_4', A_357))=A_357 | ~r1_tarski(A_357, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_1970])).
% 5.25/2.03  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.25/2.03  tff(c_1695, plain, (![A_329, B_330, C_331, D_332]: (k2_partfun1(A_329, B_330, C_331, D_332)=k7_relat_1(C_331, D_332) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(C_331))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.25/2.03  tff(c_1701, plain, (![D_332]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_332)=k7_relat_1('#skF_4', D_332) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1695])).
% 5.25/2.03  tff(c_1709, plain, (![D_332]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_332)=k7_relat_1('#skF_4', D_332))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1701])).
% 5.25/2.03  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.03  tff(c_383, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.25/2.03  tff(c_393, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_383])).
% 5.25/2.03  tff(c_606, plain, (![B_170, A_171, C_172]: (k1_xboole_0=B_170 | k1_relset_1(A_171, B_170, C_172)=A_171 | ~v1_funct_2(C_172, A_171, B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.03  tff(c_615, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_606])).
% 5.25/2.03  tff(c_624, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_393, c_615])).
% 5.25/2.03  tff(c_625, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_624])).
% 5.25/2.03  tff(c_644, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_625, c_24])).
% 5.25/2.03  tff(c_650, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_644])).
% 5.25/2.03  tff(c_482, plain, (![A_149, B_150, C_151, D_152]: (k2_partfun1(A_149, B_150, C_151, D_152)=k7_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(C_151))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.25/2.03  tff(c_486, plain, (![D_152]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_152)=k7_relat_1('#skF_4', D_152) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_482])).
% 5.25/2.03  tff(c_491, plain, (![D_152]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_152)=k7_relat_1('#skF_4', D_152))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_486])).
% 5.25/2.03  tff(c_806, plain, (![A_187, B_188, C_189, D_190]: (m1_subset_1(k2_partfun1(A_187, B_188, C_189, D_190), k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.25/2.03  tff(c_833, plain, (![D_152]: (m1_subset_1(k7_relat_1('#skF_4', D_152), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_491, c_806])).
% 5.25/2.03  tff(c_855, plain, (![D_191]: (m1_subset_1(k7_relat_1('#skF_4', D_191), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_833])).
% 5.25/2.03  tff(c_32, plain, (![D_26, B_24, C_25, A_23]: (m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(B_24, C_25))) | ~r1_tarski(k1_relat_1(D_26), B_24) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_23, C_25))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.25/2.03  tff(c_1395, plain, (![D_275, B_276]: (m1_subset_1(k7_relat_1('#skF_4', D_275), k1_zfmisc_1(k2_zfmisc_1(B_276, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_275)), B_276))), inference(resolution, [status(thm)], [c_855, c_32])).
% 5.25/2.03  tff(c_268, plain, (![A_87, B_88, C_89, D_90]: (v1_funct_1(k2_partfun1(A_87, B_88, C_89, D_90)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.25/2.03  tff(c_272, plain, (![D_90]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_90)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_268])).
% 5.25/2.03  tff(c_277, plain, (![D_90]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_90)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_272])).
% 5.25/2.03  tff(c_54, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.25/2.03  tff(c_148, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.25/2.03  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_148])).
% 5.25/2.03  tff(c_291, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 5.25/2.03  tff(c_304, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_291])).
% 5.25/2.03  tff(c_493, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_304])).
% 5.25/2.03  tff(c_1447, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_1395, c_493])).
% 5.25/2.03  tff(c_1473, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_650, c_1447])).
% 5.25/2.03  tff(c_1476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_6, c_1473])).
% 5.25/2.03  tff(c_1478, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_291])).
% 5.25/2.03  tff(c_1615, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1478, c_1602])).
% 5.25/2.03  tff(c_1712, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1709, c_1615])).
% 5.25/2.03  tff(c_1477, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_291])).
% 5.25/2.03  tff(c_1718, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1477])).
% 5.25/2.03  tff(c_1717, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_1478])).
% 5.25/2.03  tff(c_1870, plain, (![B_342, C_343, A_344]: (k1_xboole_0=B_342 | v1_funct_2(C_343, A_344, B_342) | k1_relset_1(A_344, B_342, C_343)!=A_344 | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_344, B_342))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.03  tff(c_1876, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1717, c_1870])).
% 5.25/2.03  tff(c_1891, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1718, c_71, c_1876])).
% 5.25/2.03  tff(c_1896, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1712, c_1891])).
% 5.25/2.03  tff(c_2054, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2048, c_1896])).
% 5.25/2.03  tff(c_2079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2054])).
% 5.25/2.03  tff(c_2080, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 5.25/2.03  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.25/2.03  tff(c_2093, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_14])).
% 5.25/2.03  tff(c_2081, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 5.25/2.03  tff(c_2086, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2081])).
% 5.25/2.03  tff(c_2103, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2093, c_2086, c_60])).
% 5.25/2.03  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.25/2.03  tff(c_2104, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_12])).
% 5.25/2.03  tff(c_2833, plain, (![A_503, B_504, C_505]: (k1_relset_1(A_503, B_504, C_505)=k1_relat_1(C_505) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_503, B_504))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.25/2.03  tff(c_2840, plain, (![A_506, C_507]: (k1_relset_1(A_506, '#skF_1', C_507)=k1_relat_1(C_507) | ~m1_subset_1(C_507, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2833])).
% 5.25/2.03  tff(c_2858, plain, (![A_510]: (k1_relset_1(A_510, '#skF_1', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2103, c_2840])).
% 5.25/2.03  tff(c_2087, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2086, c_62])).
% 5.25/2.03  tff(c_44, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.03  tff(c_65, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 5.25/2.03  tff(c_2848, plain, (![B_508, C_509]: (k1_relset_1('#skF_1', B_508, C_509)='#skF_1' | ~v1_funct_2(C_509, '#skF_1', B_508) | ~m1_subset_1(C_509, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_2080, c_2080, c_65])).
% 5.25/2.03  tff(c_2850, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2087, c_2848])).
% 5.25/2.03  tff(c_2853, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2850])).
% 5.25/2.03  tff(c_2862, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2858, c_2853])).
% 5.25/2.03  tff(c_2893, plain, (![B_512, C_513]: (k1_relset_1('#skF_1', B_512, C_513)=k1_relat_1(C_513) | ~m1_subset_1(C_513, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2093, c_2833])).
% 5.25/2.03  tff(c_2897, plain, (![B_512]: (k1_relset_1('#skF_1', B_512, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2103, c_2893])).
% 5.25/2.03  tff(c_2900, plain, (![B_512]: (k1_relset_1('#skF_1', B_512, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2862, c_2897])).
% 5.25/2.03  tff(c_40, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.25/2.03  tff(c_66, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 5.25/2.03  tff(c_2917, plain, (![C_515, B_516]: (v1_funct_2(C_515, '#skF_1', B_516) | k1_relset_1('#skF_1', B_516, C_515)!='#skF_1' | ~m1_subset_1(C_515, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_2080, c_2080, c_66])).
% 5.25/2.03  tff(c_2921, plain, (![B_516]: (v1_funct_2('#skF_4', '#skF_1', B_516) | k1_relset_1('#skF_1', B_516, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_2103, c_2917])).
% 5.25/2.03  tff(c_2925, plain, (![B_516]: (v1_funct_2('#skF_4', '#skF_1', B_516))), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_2921])).
% 5.25/2.03  tff(c_2094, plain, (![B_360]: (k2_zfmisc_1('#skF_1', B_360)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_14])).
% 5.25/2.03  tff(c_2098, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2094, c_18])).
% 5.25/2.03  tff(c_2161, plain, (![B_366, A_367]: (v1_relat_1(B_366) | ~m1_subset_1(B_366, k1_zfmisc_1(A_367)) | ~v1_relat_1(A_367))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.25/2.03  tff(c_2164, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2103, c_2161])).
% 5.25/2.03  tff(c_2167, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_2164])).
% 5.25/2.03  tff(c_2693, plain, (![C_485, A_486, B_487]: (v4_relat_1(C_485, A_486) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_486, B_487))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.25/2.03  tff(c_2702, plain, (![C_489, A_490]: (v4_relat_1(C_489, A_490) | ~m1_subset_1(C_489, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2693])).
% 5.25/2.03  tff(c_2706, plain, (![A_491]: (v4_relat_1('#skF_4', A_491))), inference(resolution, [status(thm)], [c_2103, c_2702])).
% 5.25/2.03  tff(c_20, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.25/2.03  tff(c_2709, plain, (![A_491]: (k7_relat_1('#skF_4', A_491)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2706, c_20])).
% 5.25/2.03  tff(c_2712, plain, (![A_491]: (k7_relat_1('#skF_4', A_491)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2709])).
% 5.25/2.03  tff(c_3001, plain, (![A_542, B_543, C_544, D_545]: (k2_partfun1(A_542, B_543, C_544, D_545)=k7_relat_1(C_544, D_545) | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(A_542, B_543))) | ~v1_funct_1(C_544))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.25/2.03  tff(c_3006, plain, (![A_546, C_547, D_548]: (k2_partfun1(A_546, '#skF_1', C_547, D_548)=k7_relat_1(C_547, D_548) | ~m1_subset_1(C_547, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_547))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_3001])).
% 5.25/2.03  tff(c_3010, plain, (![A_546, D_548]: (k2_partfun1(A_546, '#skF_1', '#skF_4', D_548)=k7_relat_1('#skF_4', D_548) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2103, c_3006])).
% 5.25/2.03  tff(c_3016, plain, (![A_546, D_548]: (k2_partfun1(A_546, '#skF_1', '#skF_4', D_548)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2712, c_3010])).
% 5.25/2.03  tff(c_2445, plain, (![C_428, A_429, B_430]: (v4_relat_1(C_428, A_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.25/2.03  tff(c_2452, plain, (![C_431, A_432]: (v4_relat_1(C_431, A_432) | ~m1_subset_1(C_431, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2445])).
% 5.25/2.03  tff(c_2458, plain, (![A_433]: (v4_relat_1('#skF_4', A_433))), inference(resolution, [status(thm)], [c_2103, c_2452])).
% 5.25/2.03  tff(c_2461, plain, (![A_433]: (k7_relat_1('#skF_4', A_433)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2458, c_20])).
% 5.25/2.03  tff(c_2464, plain, (![A_433]: (k7_relat_1('#skF_4', A_433)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2461])).
% 5.25/2.03  tff(c_2670, plain, (![A_476, B_477, C_478, D_479]: (k2_partfun1(A_476, B_477, C_478, D_479)=k7_relat_1(C_478, D_479) | ~m1_subset_1(C_478, k1_zfmisc_1(k2_zfmisc_1(A_476, B_477))) | ~v1_funct_1(C_478))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.25/2.03  tff(c_2675, plain, (![A_480, C_481, D_482]: (k2_partfun1(A_480, '#skF_1', C_481, D_482)=k7_relat_1(C_481, D_482) | ~m1_subset_1(C_481, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_481))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2670])).
% 5.25/2.03  tff(c_2677, plain, (![A_480, D_482]: (k2_partfun1(A_480, '#skF_1', '#skF_4', D_482)=k7_relat_1('#skF_4', D_482) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2103, c_2675])).
% 5.25/2.03  tff(c_2680, plain, (![A_480, D_482]: (k2_partfun1(A_480, '#skF_1', '#skF_4', D_482)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2464, c_2677])).
% 5.25/2.03  tff(c_2387, plain, (![A_408, B_409, C_410, D_411]: (v1_funct_1(k2_partfun1(A_408, B_409, C_410, D_411)) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_408, B_409))) | ~v1_funct_1(C_410))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.25/2.03  tff(c_2392, plain, (![A_412, C_413, D_414]: (v1_funct_1(k2_partfun1(A_412, '#skF_1', C_413, D_414)) | ~m1_subset_1(C_413, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_413))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_2387])).
% 5.25/2.03  tff(c_2394, plain, (![A_412, D_414]: (v1_funct_1(k2_partfun1(A_412, '#skF_1', '#skF_4', D_414)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2103, c_2392])).
% 5.25/2.03  tff(c_2397, plain, (![A_412, D_414]: (v1_funct_1(k2_partfun1(A_412, '#skF_1', '#skF_4', D_414)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2394])).
% 5.25/2.03  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.25/2.03  tff(c_2124, plain, (![A_362]: (A_362='#skF_1' | ~r1_tarski(A_362, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_2080, c_8])).
% 5.25/2.03  tff(c_2134, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_58, c_2124])).
% 5.25/2.03  tff(c_2168, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2134, c_2086, c_2134, c_2134, c_2086, c_2086, c_2134, c_2104, c_2086, c_2086, c_54])).
% 5.25/2.03  tff(c_2169, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2168])).
% 5.25/2.03  tff(c_2400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2397, c_2169])).
% 5.25/2.03  tff(c_2401, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_2168])).
% 5.25/2.03  tff(c_2438, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2401])).
% 5.25/2.03  tff(c_2682, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2680, c_2438])).
% 5.25/2.03  tff(c_2686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2103, c_2682])).
% 5.25/2.03  tff(c_2687, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2401])).
% 5.25/2.03  tff(c_3023, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3016, c_2687])).
% 5.25/2.03  tff(c_3036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2925, c_3023])).
% 5.25/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.03  
% 5.25/2.03  Inference rules
% 5.25/2.03  ----------------------
% 5.25/2.03  #Ref     : 0
% 5.25/2.03  #Sup     : 660
% 5.25/2.03  #Fact    : 0
% 5.25/2.03  #Define  : 0
% 5.25/2.03  #Split   : 19
% 5.25/2.03  #Chain   : 0
% 5.25/2.03  #Close   : 0
% 5.25/2.03  
% 5.25/2.03  Ordering : KBO
% 5.25/2.03  
% 5.25/2.03  Simplification rules
% 5.25/2.03  ----------------------
% 5.25/2.03  #Subsume      : 65
% 5.25/2.03  #Demod        : 538
% 5.25/2.03  #Tautology    : 322
% 5.25/2.03  #SimpNegUnit  : 19
% 5.25/2.03  #BackRed      : 55
% 5.25/2.03  
% 5.25/2.03  #Partial instantiations: 0
% 5.25/2.03  #Strategies tried      : 1
% 5.25/2.03  
% 5.25/2.03  Timing (in seconds)
% 5.25/2.03  ----------------------
% 5.25/2.04  Preprocessing        : 0.37
% 5.25/2.04  Parsing              : 0.20
% 5.25/2.04  CNF conversion       : 0.02
% 5.25/2.04  Main loop            : 0.86
% 5.25/2.04  Inferencing          : 0.33
% 5.25/2.04  Reduction            : 0.28
% 5.25/2.04  Demodulation         : 0.20
% 5.25/2.04  BG Simplification    : 0.03
% 5.25/2.04  Subsumption          : 0.14
% 5.25/2.04  Abstraction          : 0.04
% 5.25/2.04  MUC search           : 0.00
% 5.25/2.04  Cooper               : 0.00
% 5.25/2.04  Total                : 1.29
% 5.25/2.04  Index Insertion      : 0.00
% 5.25/2.04  Index Deletion       : 0.00
% 5.25/2.04  Index Matching       : 0.00
% 5.25/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
