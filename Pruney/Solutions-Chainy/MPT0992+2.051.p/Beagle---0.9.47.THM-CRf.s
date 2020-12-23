%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:38 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  164 (1246 expanded)
%              Number of leaves         :   36 ( 388 expanded)
%              Depth                    :   12
%              Number of atoms          :  260 (3715 expanded)
%              Number of equality atoms :   77 (1245 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_54,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_76,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1491,plain,(
    ! [A_231,B_232,C_233] :
      ( k1_relset_1(A_231,B_232,C_233) = k1_relat_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1503,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1491])).

tff(c_1753,plain,(
    ! [B_276,A_277,C_278] :
      ( k1_xboole_0 = B_276
      | k1_relset_1(A_277,B_276,C_278) = A_277
      | ~ v1_funct_2(C_278,A_277,B_276)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_277,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1762,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1753])).

tff(c_1775,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1503,c_1762])).

tff(c_1776,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1775])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k7_relat_1(B_12,A_11)) = A_11
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1794,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1776,c_20])).

tff(c_1905,plain,(
    ! [A_285] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_285)) = A_285
      | ~ r1_tarski(A_285,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1794])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1611,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k2_partfun1(A_258,B_259,C_260,D_261) = k7_relat_1(C_260,D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1615,plain,(
    ! [D_261] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_261) = k7_relat_1('#skF_4',D_261)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_1611])).

tff(c_1624,plain,(
    ! [D_261] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_261) = k7_relat_1('#skF_4',D_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1615])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_393,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_401,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_393])).

tff(c_636,plain,(
    ! [B_147,A_148,C_149] :
      ( k1_xboole_0 = B_147
      | k1_relset_1(A_148,B_147,C_149) = A_148
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_642,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_636])).

tff(c_652,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_401,c_642])).

tff(c_653,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_652])).

tff(c_674,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_20])).

tff(c_680,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_674])).

tff(c_497,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k2_partfun1(A_120,B_121,C_122,D_123) = k7_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_499,plain,(
    ! [D_123] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_123) = k7_relat_1('#skF_4',D_123)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_497])).

tff(c_505,plain,(
    ! [D_123] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_123) = k7_relat_1('#skF_4',D_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_499])).

tff(c_818,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( m1_subset_1(k2_partfun1(A_154,B_155,C_156,D_157),k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_856,plain,(
    ! [D_123] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_123),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_818])).

tff(c_871,plain,(
    ! [D_158] : m1_subset_1(k7_relat_1('#skF_4',D_158),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_856])).

tff(c_28,plain,(
    ! [D_26,B_24,C_25,A_23] :
      ( m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(B_24,C_25)))
      | ~ r1_tarski(k1_relat_1(D_26),B_24)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k2_zfmisc_1(A_23,C_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1323,plain,(
    ! [D_225,B_226] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_225),k1_zfmisc_1(k2_zfmisc_1(B_226,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_225)),B_226) ) ),
    inference(resolution,[status(thm)],[c_871,c_28])).

tff(c_256,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( v1_funct_1(k2_partfun1(A_74,B_75,C_76,D_77))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_258,plain,(
    ! [D_77] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_77))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_256])).

tff(c_264,plain,(
    ! [D_77] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_258])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_134,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_134])).

tff(c_280,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_320,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_509,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_320])).

tff(c_1385,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1323,c_509])).

tff(c_1401,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_1385])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10,c_1401])).

tff(c_1405,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_1633,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1405])).

tff(c_1406,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_1502,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1406,c_1491])).

tff(c_1628,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1624,c_1502])).

tff(c_1632,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1406])).

tff(c_1879,plain,(
    ! [B_282,C_283,A_284] :
      ( k1_xboole_0 = B_282
      | v1_funct_2(C_283,A_284,B_282)
      | k1_relset_1(A_284,B_282,C_283) != A_284
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1885,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1632,c_1879])).

tff(c_1897,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_1885])).

tff(c_1898,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1633,c_73,c_1897])).

tff(c_1911,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1905,c_1898])).

tff(c_1947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1911])).

tff(c_1948,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1953,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_2])).

tff(c_1949,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1958,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_1949])).

tff(c_1959,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_56])).

tff(c_2652,plain,(
    ! [C_392,A_393,B_394] :
      ( v1_xboole_0(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_xboole_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2658,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1959,c_2652])).

tff(c_2668,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_2658])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1951,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_4])).

tff(c_2674,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2668,c_1951])).

tff(c_1960,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_58])).

tff(c_2685,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2674,c_2674,c_1960])).

tff(c_2351,plain,(
    ! [C_340,A_341,B_342] :
      ( v1_xboole_0(C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342)))
      | ~ v1_xboole_0(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2354,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1959,c_2351])).

tff(c_2361,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_2354])).

tff(c_2367,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2361,c_1951])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1950,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_14])).

tff(c_2376,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2367,c_1950])).

tff(c_2325,plain,(
    ! [C_336,A_337,B_338] :
      ( v1_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2334,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1950,c_2325])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k7_relat_1(B_10,A_9),B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1952,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1948,c_12])).

tff(c_2282,plain,(
    ! [B_333,A_334] :
      ( B_333 = A_334
      | ~ r1_tarski(B_333,A_334)
      | ~ r1_tarski(A_334,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2307,plain,(
    ! [A_335] :
      ( A_335 = '#skF_1'
      | ~ r1_tarski(A_335,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1952,c_2282])).

tff(c_2320,plain,(
    ! [A_9] :
      ( k7_relat_1('#skF_1',A_9) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_2307])).

tff(c_2338,plain,(
    ! [A_9] : k7_relat_1('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_2320])).

tff(c_2368,plain,(
    ! [A_9] : k7_relat_1('#skF_4',A_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2367,c_2367,c_2338])).

tff(c_2612,plain,(
    ! [A_383,B_384,C_385,D_386] :
      ( k2_partfun1(A_383,B_384,C_385,D_386) = k7_relat_1(C_385,D_386)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384)))
      | ~ v1_funct_1(C_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2615,plain,(
    ! [A_383,B_384,D_386] :
      ( k2_partfun1(A_383,B_384,'#skF_4',D_386) = k7_relat_1('#skF_4',D_386)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2376,c_2612])).

tff(c_2618,plain,(
    ! [A_383,B_384,D_386] : k2_partfun1(A_383,B_384,'#skF_4',D_386) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2368,c_2615])).

tff(c_2290,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2282])).

tff(c_2299,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_2290])).

tff(c_2054,plain,(
    ! [C_305,A_306,B_307] :
      ( v1_xboole_0(C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307)))
      | ~ v1_xboole_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2057,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1959,c_2054])).

tff(c_2064,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_2057])).

tff(c_2070,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2064,c_1951])).

tff(c_2081,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2070,c_1950])).

tff(c_2270,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( v1_funct_1(k2_partfun1(A_329,B_330,C_331,D_332))
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2273,plain,(
    ! [A_329,B_330,D_332] :
      ( v1_funct_1(k2_partfun1(A_329,B_330,'#skF_4',D_332))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2081,c_2270])).

tff(c_2276,plain,(
    ! [A_329,B_330,D_332] : v1_funct_1(k2_partfun1(A_329,B_330,'#skF_4',D_332)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2273])).

tff(c_1978,plain,(
    ! [B_292,A_293] :
      ( B_292 = A_293
      | ~ r1_tarski(B_292,A_293)
      | ~ r1_tarski(A_293,B_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1986,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1978])).

tff(c_1995,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1986])).

tff(c_1976,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1958,c_1958,c_1958,c_1958,c_1958,c_50])).

tff(c_1977,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1976])).

tff(c_1996,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1977])).

tff(c_2075,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2070,c_2070,c_2070,c_1996])).

tff(c_2279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2276,c_2075])).

tff(c_2280,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1976])).

tff(c_2335,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2299,c_2299,c_2299,c_2299,c_2280])).

tff(c_2336,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2335])).

tff(c_2477,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2367,c_2367,c_2367,c_2367,c_2367,c_2336])).

tff(c_2627,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2477])).

tff(c_2631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2376,c_2627])).

tff(c_2633,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2335])).

tff(c_2655,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2633,c_2652])).

tff(c_2665,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_2655])).

tff(c_2787,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2674,c_2674,c_2674,c_2665])).

tff(c_2687,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2674,c_1951])).

tff(c_2791,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2787,c_2687])).

tff(c_2632,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2335])).

tff(c_2677,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2674,c_2674,c_2674,c_2674,c_2674,c_2632])).

tff(c_2845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2685,c_2791,c_2677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.75  
% 4.32/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.76  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.32/1.76  
% 4.32/1.76  %Foreground sorts:
% 4.32/1.76  
% 4.32/1.76  
% 4.32/1.76  %Background operators:
% 4.32/1.76  
% 4.32/1.76  
% 4.32/1.76  %Foreground operators:
% 4.32/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.32/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.32/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.32/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.32/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.32/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.32/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.32/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.32/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.32/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.32/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.32/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.32/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.76  
% 4.39/1.78  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 4.39/1.78  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.39/1.78  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.39/1.78  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.39/1.78  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 4.39/1.78  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.39/1.78  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.39/1.78  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.39/1.78  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.39/1.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.39/1.78  tff(f_67, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.39/1.78  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.39/1.78  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.39/1.78  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.39/1.78  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.39/1.78  tff(c_54, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.39/1.78  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.39/1.78  tff(c_76, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.39/1.78  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_76])).
% 4.39/1.78  tff(c_52, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.39/1.78  tff(c_73, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 4.39/1.78  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.39/1.78  tff(c_1491, plain, (![A_231, B_232, C_233]: (k1_relset_1(A_231, B_232, C_233)=k1_relat_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.39/1.78  tff(c_1503, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_1491])).
% 4.39/1.78  tff(c_1753, plain, (![B_276, A_277, C_278]: (k1_xboole_0=B_276 | k1_relset_1(A_277, B_276, C_278)=A_277 | ~v1_funct_2(C_278, A_277, B_276) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_277, B_276))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.39/1.78  tff(c_1762, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1753])).
% 4.39/1.78  tff(c_1775, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1503, c_1762])).
% 4.39/1.78  tff(c_1776, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_1775])).
% 4.39/1.78  tff(c_20, plain, (![B_12, A_11]: (k1_relat_1(k7_relat_1(B_12, A_11))=A_11 | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.39/1.78  tff(c_1794, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1776, c_20])).
% 4.39/1.78  tff(c_1905, plain, (![A_285]: (k1_relat_1(k7_relat_1('#skF_4', A_285))=A_285 | ~r1_tarski(A_285, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1794])).
% 4.39/1.78  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.39/1.78  tff(c_1611, plain, (![A_258, B_259, C_260, D_261]: (k2_partfun1(A_258, B_259, C_260, D_261)=k7_relat_1(C_260, D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.39/1.78  tff(c_1615, plain, (![D_261]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_261)=k7_relat_1('#skF_4', D_261) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1611])).
% 4.39/1.78  tff(c_1624, plain, (![D_261]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_261)=k7_relat_1('#skF_4', D_261))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1615])).
% 4.39/1.78  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.39/1.78  tff(c_393, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.39/1.78  tff(c_401, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_393])).
% 4.39/1.78  tff(c_636, plain, (![B_147, A_148, C_149]: (k1_xboole_0=B_147 | k1_relset_1(A_148, B_147, C_149)=A_148 | ~v1_funct_2(C_149, A_148, B_147) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.39/1.78  tff(c_642, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_636])).
% 4.39/1.78  tff(c_652, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_401, c_642])).
% 4.39/1.78  tff(c_653, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_73, c_652])).
% 4.39/1.78  tff(c_674, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_653, c_20])).
% 4.39/1.78  tff(c_680, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_674])).
% 4.39/1.78  tff(c_497, plain, (![A_120, B_121, C_122, D_123]: (k2_partfun1(A_120, B_121, C_122, D_123)=k7_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.39/1.78  tff(c_499, plain, (![D_123]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_123)=k7_relat_1('#skF_4', D_123) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_497])).
% 4.39/1.78  tff(c_505, plain, (![D_123]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_123)=k7_relat_1('#skF_4', D_123))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_499])).
% 4.39/1.78  tff(c_818, plain, (![A_154, B_155, C_156, D_157]: (m1_subset_1(k2_partfun1(A_154, B_155, C_156, D_157), k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_1(C_156))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.39/1.78  tff(c_856, plain, (![D_123]: (m1_subset_1(k7_relat_1('#skF_4', D_123), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_818])).
% 4.39/1.78  tff(c_871, plain, (![D_158]: (m1_subset_1(k7_relat_1('#skF_4', D_158), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_856])).
% 4.39/1.78  tff(c_28, plain, (![D_26, B_24, C_25, A_23]: (m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(B_24, C_25))) | ~r1_tarski(k1_relat_1(D_26), B_24) | ~m1_subset_1(D_26, k1_zfmisc_1(k2_zfmisc_1(A_23, C_25))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.39/1.78  tff(c_1323, plain, (![D_225, B_226]: (m1_subset_1(k7_relat_1('#skF_4', D_225), k1_zfmisc_1(k2_zfmisc_1(B_226, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_225)), B_226))), inference(resolution, [status(thm)], [c_871, c_28])).
% 4.39/1.78  tff(c_256, plain, (![A_74, B_75, C_76, D_77]: (v1_funct_1(k2_partfun1(A_74, B_75, C_76, D_77)) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_1(C_76))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.39/1.78  tff(c_258, plain, (![D_77]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_77)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_256])).
% 4.39/1.78  tff(c_264, plain, (![D_77]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_77)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_258])).
% 4.39/1.78  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.39/1.78  tff(c_134, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.39/1.78  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_134])).
% 4.39/1.78  tff(c_280, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_50])).
% 4.39/1.78  tff(c_320, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_280])).
% 4.39/1.78  tff(c_509, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_320])).
% 4.39/1.78  tff(c_1385, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_1323, c_509])).
% 4.39/1.78  tff(c_1401, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_680, c_1385])).
% 4.39/1.78  tff(c_1404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_10, c_1401])).
% 4.39/1.78  tff(c_1405, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_280])).
% 4.39/1.78  tff(c_1633, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1405])).
% 4.39/1.78  tff(c_1406, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_280])).
% 4.39/1.78  tff(c_1502, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1406, c_1491])).
% 4.39/1.78  tff(c_1628, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1624, c_1502])).
% 4.39/1.78  tff(c_1632, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1406])).
% 4.39/1.78  tff(c_1879, plain, (![B_282, C_283, A_284]: (k1_xboole_0=B_282 | v1_funct_2(C_283, A_284, B_282) | k1_relset_1(A_284, B_282, C_283)!=A_284 | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, B_282))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.39/1.78  tff(c_1885, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1632, c_1879])).
% 4.39/1.78  tff(c_1897, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1628, c_1885])).
% 4.39/1.78  tff(c_1898, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1633, c_73, c_1897])).
% 4.39/1.78  tff(c_1911, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1905, c_1898])).
% 4.39/1.78  tff(c_1947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1911])).
% 4.39/1.78  tff(c_1948, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 4.39/1.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.39/1.78  tff(c_1953, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_2])).
% 4.39/1.78  tff(c_1949, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 4.39/1.78  tff(c_1958, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_1949])).
% 4.39/1.78  tff(c_1959, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_56])).
% 4.39/1.78  tff(c_2652, plain, (![C_392, A_393, B_394]: (v1_xboole_0(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_xboole_0(A_393))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.39/1.78  tff(c_2658, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1959, c_2652])).
% 4.39/1.78  tff(c_2668, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_2658])).
% 4.39/1.78  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.39/1.78  tff(c_1951, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_4])).
% 4.39/1.78  tff(c_2674, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2668, c_1951])).
% 4.39/1.78  tff(c_1960, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_58])).
% 4.39/1.78  tff(c_2685, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2674, c_2674, c_1960])).
% 4.39/1.78  tff(c_2351, plain, (![C_340, A_341, B_342]: (v1_xboole_0(C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))) | ~v1_xboole_0(A_341))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.39/1.78  tff(c_2354, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1959, c_2351])).
% 4.39/1.78  tff(c_2361, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_2354])).
% 4.39/1.78  tff(c_2367, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2361, c_1951])).
% 4.39/1.78  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.39/1.78  tff(c_1950, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_14])).
% 4.39/1.78  tff(c_2376, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2367, c_1950])).
% 4.39/1.78  tff(c_2325, plain, (![C_336, A_337, B_338]: (v1_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.39/1.78  tff(c_2334, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1950, c_2325])).
% 4.39/1.78  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k7_relat_1(B_10, A_9), B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.39/1.78  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.39/1.78  tff(c_1952, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_1948, c_12])).
% 4.39/1.78  tff(c_2282, plain, (![B_333, A_334]: (B_333=A_334 | ~r1_tarski(B_333, A_334) | ~r1_tarski(A_334, B_333))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.39/1.78  tff(c_2307, plain, (![A_335]: (A_335='#skF_1' | ~r1_tarski(A_335, '#skF_1'))), inference(resolution, [status(thm)], [c_1952, c_2282])).
% 4.39/1.78  tff(c_2320, plain, (![A_9]: (k7_relat_1('#skF_1', A_9)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_2307])).
% 4.39/1.78  tff(c_2338, plain, (![A_9]: (k7_relat_1('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_2320])).
% 4.39/1.78  tff(c_2368, plain, (![A_9]: (k7_relat_1('#skF_4', A_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2367, c_2367, c_2338])).
% 4.39/1.78  tff(c_2612, plain, (![A_383, B_384, C_385, D_386]: (k2_partfun1(A_383, B_384, C_385, D_386)=k7_relat_1(C_385, D_386) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))) | ~v1_funct_1(C_385))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.39/1.78  tff(c_2615, plain, (![A_383, B_384, D_386]: (k2_partfun1(A_383, B_384, '#skF_4', D_386)=k7_relat_1('#skF_4', D_386) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2376, c_2612])).
% 4.39/1.78  tff(c_2618, plain, (![A_383, B_384, D_386]: (k2_partfun1(A_383, B_384, '#skF_4', D_386)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2368, c_2615])).
% 4.39/1.78  tff(c_2290, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_2282])).
% 4.39/1.78  tff(c_2299, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_2290])).
% 4.39/1.78  tff(c_2054, plain, (![C_305, A_306, B_307]: (v1_xboole_0(C_305) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))) | ~v1_xboole_0(A_306))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.39/1.78  tff(c_2057, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1959, c_2054])).
% 4.39/1.78  tff(c_2064, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_2057])).
% 4.39/1.78  tff(c_2070, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2064, c_1951])).
% 4.39/1.78  tff(c_2081, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2070, c_1950])).
% 4.39/1.78  tff(c_2270, plain, (![A_329, B_330, C_331, D_332]: (v1_funct_1(k2_partfun1(A_329, B_330, C_331, D_332)) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(C_331))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.39/1.78  tff(c_2273, plain, (![A_329, B_330, D_332]: (v1_funct_1(k2_partfun1(A_329, B_330, '#skF_4', D_332)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2081, c_2270])).
% 4.39/1.78  tff(c_2276, plain, (![A_329, B_330, D_332]: (v1_funct_1(k2_partfun1(A_329, B_330, '#skF_4', D_332)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2273])).
% 4.39/1.78  tff(c_1978, plain, (![B_292, A_293]: (B_292=A_293 | ~r1_tarski(B_292, A_293) | ~r1_tarski(A_293, B_292))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.39/1.78  tff(c_1986, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1978])).
% 4.39/1.78  tff(c_1995, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1986])).
% 4.39/1.78  tff(c_1976, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1958, c_1958, c_1958, c_1958, c_1958, c_50])).
% 4.39/1.78  tff(c_1977, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1976])).
% 4.39/1.78  tff(c_1996, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1977])).
% 4.39/1.78  tff(c_2075, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2070, c_2070, c_2070, c_1996])).
% 4.39/1.78  tff(c_2279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2276, c_2075])).
% 4.39/1.78  tff(c_2280, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_1976])).
% 4.39/1.78  tff(c_2335, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2299, c_2299, c_2299, c_2299, c_2280])).
% 4.39/1.78  tff(c_2336, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2335])).
% 4.39/1.78  tff(c_2477, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2367, c_2367, c_2367, c_2367, c_2367, c_2336])).
% 4.39/1.78  tff(c_2627, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2618, c_2477])).
% 4.39/1.78  tff(c_2631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2376, c_2627])).
% 4.39/1.78  tff(c_2633, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_2335])).
% 4.39/1.78  tff(c_2655, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2633, c_2652])).
% 4.39/1.78  tff(c_2665, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_2655])).
% 4.39/1.78  tff(c_2787, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2674, c_2674, c_2674, c_2665])).
% 4.39/1.78  tff(c_2687, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2674, c_1951])).
% 4.39/1.78  tff(c_2791, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2787, c_2687])).
% 4.39/1.78  tff(c_2632, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2335])).
% 4.39/1.78  tff(c_2677, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2674, c_2674, c_2674, c_2674, c_2674, c_2632])).
% 4.39/1.78  tff(c_2845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2685, c_2791, c_2677])).
% 4.39/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.78  
% 4.39/1.78  Inference rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Ref     : 0
% 4.39/1.78  #Sup     : 575
% 4.39/1.78  #Fact    : 0
% 4.39/1.78  #Define  : 0
% 4.39/1.78  #Split   : 17
% 4.39/1.78  #Chain   : 0
% 4.39/1.78  #Close   : 0
% 4.39/1.78  
% 4.39/1.78  Ordering : KBO
% 4.39/1.78  
% 4.39/1.78  Simplification rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Subsume      : 66
% 4.39/1.78  #Demod        : 515
% 4.39/1.78  #Tautology    : 278
% 4.39/1.78  #SimpNegUnit  : 20
% 4.39/1.78  #BackRed      : 96
% 4.39/1.78  
% 4.39/1.78  #Partial instantiations: 0
% 4.39/1.78  #Strategies tried      : 1
% 4.39/1.78  
% 4.39/1.78  Timing (in seconds)
% 4.39/1.78  ----------------------
% 4.39/1.78  Preprocessing        : 0.34
% 4.39/1.78  Parsing              : 0.18
% 4.39/1.78  CNF conversion       : 0.02
% 4.39/1.78  Main loop            : 0.66
% 4.39/1.78  Inferencing          : 0.24
% 4.39/1.78  Reduction            : 0.21
% 4.39/1.78  Demodulation         : 0.15
% 4.39/1.78  BG Simplification    : 0.03
% 4.39/1.78  Subsumption          : 0.12
% 4.39/1.78  Abstraction          : 0.03
% 4.39/1.78  MUC search           : 0.00
% 4.39/1.78  Cooper               : 0.00
% 4.39/1.78  Total                : 1.04
% 4.39/1.78  Index Insertion      : 0.00
% 4.39/1.78  Index Deletion       : 0.00
% 4.39/1.78  Index Matching       : 0.00
% 4.39/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
