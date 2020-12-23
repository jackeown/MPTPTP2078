%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 5.83s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 262 expanded)
%              Number of leaves         :   47 ( 107 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 ( 512 expanded)
%              Number of equality atoms :   73 ( 220 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_142,axiom,(
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

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_180,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_193,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_180])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_202,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_193,c_46])).

tff(c_214,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_616,plain,(
    ! [B_157,A_158] :
      ( k1_tarski(k1_funct_1(B_157,A_158)) = k2_relat_1(B_157)
      | k1_tarski(A_158) != k1_relat_1(B_157)
      | ~ v1_funct_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_589,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_relset_1(A_152,B_153,C_154) = k2_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_602,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_589])).

tff(c_78,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_611,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_78])).

tff(c_622,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_611])).

tff(c_632,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_86,c_622])).

tff(c_241,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_254,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_241])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_relat_1(B_27),A_26)
      | ~ v4_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_485,plain,(
    ! [B_135,A_136] :
      ( k1_tarski(B_135) = A_136
      | k1_xboole_0 = A_136
      | ~ r1_tarski(A_136,k1_tarski(B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2838,plain,(
    ! [B_358,B_359] :
      ( k1_tarski(B_358) = k1_relat_1(B_359)
      | k1_relat_1(B_359) = k1_xboole_0
      | ~ v4_relat_1(B_359,k1_tarski(B_358))
      | ~ v1_relat_1(B_359) ) ),
    inference(resolution,[status(thm)],[c_42,c_485])).

tff(c_2884,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_254,c_2838])).

tff(c_2909,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_2884])).

tff(c_2911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_632,c_2909])).

tff(c_2912,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_2913,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_2935,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2912,c_2913])).

tff(c_3419,plain,(
    ! [B_454,A_455] :
      ( k1_tarski(k1_funct_1(B_454,A_455)) = k2_relat_1(B_454)
      | k1_tarski(A_455) != k1_relat_1(B_454)
      | ~ v1_funct_1(B_454)
      | ~ v1_relat_1(B_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2922,plain,(
    ! [A_17] : m1_subset_1('#skF_4',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2912,c_30])).

tff(c_3311,plain,(
    ! [A_432,B_433,C_434] :
      ( k2_relset_1(A_432,B_433,C_434) = k2_relat_1(C_434)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3320,plain,(
    ! [A_432,B_433] : k2_relset_1(A_432,B_433,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2922,c_3311])).

tff(c_3322,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3320,c_78])).

tff(c_3425,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3419,c_3322])).

tff(c_3435,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_86,c_2935,c_3425])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2924,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2912,c_80])).

tff(c_84,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3339,plain,(
    ! [A_439,B_440,C_441,D_442] :
      ( k8_relset_1(A_439,B_440,C_441,D_442) = k10_relat_1(C_441,D_442)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_439,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3346,plain,(
    ! [A_439,B_440,D_442] : k8_relset_1(A_439,B_440,'#skF_4',D_442) = k10_relat_1('#skF_4',D_442) ),
    inference(resolution,[status(thm)],[c_2922,c_3339])).

tff(c_3543,plain,(
    ! [A_467,B_468,C_469,D_470] :
      ( m1_subset_1(k8_relset_1(A_467,B_468,C_469,D_470),k1_zfmisc_1(A_467))
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3587,plain,(
    ! [D_442,A_439,B_440] :
      ( m1_subset_1(k10_relat_1('#skF_4',D_442),k1_zfmisc_1(A_439))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_439,B_440))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3346,c_3543])).

tff(c_3605,plain,(
    ! [D_471,A_472] : m1_subset_1(k10_relat_1('#skF_4',D_471),k1_zfmisc_1(A_472)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2922,c_3587])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3689,plain,(
    ! [D_478,A_479] : r1_tarski(k10_relat_1('#skF_4',D_478),A_479) ),
    inference(resolution,[status(thm)],[c_3605,c_32])).

tff(c_120,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_147,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_155,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_124,c_147])).

tff(c_2915,plain,(
    ! [A_17] :
      ( A_17 = '#skF_4'
      | ~ r1_tarski(A_17,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2912,c_2912,c_155])).

tff(c_3739,plain,(
    ! [D_478] : k10_relat_1('#skF_4',D_478) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3689,c_2915])).

tff(c_3745,plain,(
    ! [A_439,B_440,D_442] : k8_relset_1(A_439,B_440,'#skF_4',D_442) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3739,c_3346])).

tff(c_3848,plain,(
    ! [B_494,A_495,C_496] :
      ( k8_relset_1(B_494,A_495,C_496,k7_relset_1(B_494,A_495,C_496,B_494)) = k1_relset_1(B_494,A_495,C_496)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(B_494,A_495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3856,plain,(
    ! [B_494,A_495] : k8_relset_1(B_494,A_495,'#skF_4',k7_relset_1(B_494,A_495,'#skF_4',B_494)) = k1_relset_1(B_494,A_495,'#skF_4') ),
    inference(resolution,[status(thm)],[c_2922,c_3848])).

tff(c_3862,plain,(
    ! [B_494,A_495] : k1_relset_1(B_494,A_495,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3745,c_3856])).

tff(c_76,plain,(
    ! [B_52,A_51,C_53] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_51,B_52,C_53) = A_51
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3821,plain,(
    ! [B_490,A_491,C_492] :
      ( B_490 = '#skF_4'
      | k1_relset_1(A_491,B_490,C_492) = A_491
      | ~ v1_funct_2(C_492,A_491,B_490)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(A_491,B_490))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2912,c_76])).

tff(c_3838,plain,(
    ! [B_490,A_491] :
      ( B_490 = '#skF_4'
      | k1_relset_1(A_491,B_490,'#skF_4') = A_491
      | ~ v1_funct_2('#skF_4',A_491,B_490) ) ),
    inference(resolution,[status(thm)],[c_2922,c_3821])).

tff(c_5995,plain,(
    ! [B_671,A_672] :
      ( B_671 = '#skF_4'
      | A_672 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_672,B_671) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3862,c_3838])).

tff(c_6004,plain,
    ( '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_5995])).

tff(c_6012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3435,c_2924,c_6004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n012.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:39:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.83/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.83/2.16  
% 5.83/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.83/2.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.83/2.16  
% 5.83/2.16  %Foreground sorts:
% 5.83/2.16  
% 5.83/2.16  
% 5.83/2.16  %Background operators:
% 5.83/2.16  
% 5.83/2.16  
% 5.83/2.16  %Foreground operators:
% 5.83/2.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.83/2.16  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.83/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.83/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.83/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.83/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.83/2.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.83/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.83/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.83/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.83/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.83/2.16  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.83/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.83/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.83/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.83/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.83/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.83/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.83/2.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.83/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.83/2.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.83/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.83/2.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.83/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.83/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.83/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.83/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.83/2.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.83/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.83/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.83/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.83/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.83/2.16  
% 6.16/2.18  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 6.16/2.18  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.16/2.18  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.16/2.18  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.16/2.18  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.16/2.18  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.16/2.18  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.16/2.18  tff(f_55, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.16/2.18  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.16/2.18  tff(f_118, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.16/2.18  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 6.16/2.18  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.16/2.18  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.16/2.18  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 6.16/2.18  tff(f_142, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.16/2.18  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.16/2.18  tff(c_180, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.16/2.18  tff(c_193, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_180])).
% 6.16/2.18  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.16/2.18  tff(c_46, plain, (![A_28]: (k1_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.16/2.18  tff(c_202, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_193, c_46])).
% 6.16/2.18  tff(c_214, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_202])).
% 6.16/2.18  tff(c_616, plain, (![B_157, A_158]: (k1_tarski(k1_funct_1(B_157, A_158))=k2_relat_1(B_157) | k1_tarski(A_158)!=k1_relat_1(B_157) | ~v1_funct_1(B_157) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.16/2.18  tff(c_589, plain, (![A_152, B_153, C_154]: (k2_relset_1(A_152, B_153, C_154)=k2_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.16/2.18  tff(c_602, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_589])).
% 6.16/2.18  tff(c_78, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.16/2.18  tff(c_611, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_602, c_78])).
% 6.16/2.18  tff(c_622, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_616, c_611])).
% 6.16/2.18  tff(c_632, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_86, c_622])).
% 6.16/2.18  tff(c_241, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.16/2.18  tff(c_254, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_82, c_241])).
% 6.16/2.18  tff(c_42, plain, (![B_27, A_26]: (r1_tarski(k1_relat_1(B_27), A_26) | ~v4_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.16/2.18  tff(c_485, plain, (![B_135, A_136]: (k1_tarski(B_135)=A_136 | k1_xboole_0=A_136 | ~r1_tarski(A_136, k1_tarski(B_135)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.16/2.18  tff(c_2838, plain, (![B_358, B_359]: (k1_tarski(B_358)=k1_relat_1(B_359) | k1_relat_1(B_359)=k1_xboole_0 | ~v4_relat_1(B_359, k1_tarski(B_358)) | ~v1_relat_1(B_359))), inference(resolution, [status(thm)], [c_42, c_485])).
% 6.16/2.18  tff(c_2884, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_254, c_2838])).
% 6.16/2.18  tff(c_2909, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_193, c_2884])).
% 6.16/2.18  tff(c_2911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_632, c_2909])).
% 6.16/2.18  tff(c_2912, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_202])).
% 6.16/2.18  tff(c_2913, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_202])).
% 6.16/2.18  tff(c_2935, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2912, c_2913])).
% 6.16/2.18  tff(c_3419, plain, (![B_454, A_455]: (k1_tarski(k1_funct_1(B_454, A_455))=k2_relat_1(B_454) | k1_tarski(A_455)!=k1_relat_1(B_454) | ~v1_funct_1(B_454) | ~v1_relat_1(B_454))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.16/2.18  tff(c_30, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.16/2.18  tff(c_2922, plain, (![A_17]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_2912, c_30])).
% 6.16/2.18  tff(c_3311, plain, (![A_432, B_433, C_434]: (k2_relset_1(A_432, B_433, C_434)=k2_relat_1(C_434) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.16/2.18  tff(c_3320, plain, (![A_432, B_433]: (k2_relset_1(A_432, B_433, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2922, c_3311])).
% 6.16/2.18  tff(c_3322, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3320, c_78])).
% 6.16/2.18  tff(c_3425, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3419, c_3322])).
% 6.16/2.18  tff(c_3435, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_86, c_2935, c_3425])).
% 6.16/2.18  tff(c_80, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.16/2.18  tff(c_2924, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2912, c_80])).
% 6.16/2.18  tff(c_84, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.16/2.18  tff(c_3339, plain, (![A_439, B_440, C_441, D_442]: (k8_relset_1(A_439, B_440, C_441, D_442)=k10_relat_1(C_441, D_442) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.16/2.18  tff(c_3346, plain, (![A_439, B_440, D_442]: (k8_relset_1(A_439, B_440, '#skF_4', D_442)=k10_relat_1('#skF_4', D_442))), inference(resolution, [status(thm)], [c_2922, c_3339])).
% 6.16/2.18  tff(c_3543, plain, (![A_467, B_468, C_469, D_470]: (m1_subset_1(k8_relset_1(A_467, B_468, C_469, D_470), k1_zfmisc_1(A_467)) | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.16/2.18  tff(c_3587, plain, (![D_442, A_439, B_440]: (m1_subset_1(k10_relat_1('#skF_4', D_442), k1_zfmisc_1(A_439)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_439, B_440))))), inference(superposition, [status(thm), theory('equality')], [c_3346, c_3543])).
% 6.16/2.18  tff(c_3605, plain, (![D_471, A_472]: (m1_subset_1(k10_relat_1('#skF_4', D_471), k1_zfmisc_1(A_472)))), inference(demodulation, [status(thm), theory('equality')], [c_2922, c_3587])).
% 6.16/2.18  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.16/2.18  tff(c_3689, plain, (![D_478, A_479]: (r1_tarski(k10_relat_1('#skF_4', D_478), A_479))), inference(resolution, [status(thm)], [c_3605, c_32])).
% 6.16/2.18  tff(c_120, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.16/2.18  tff(c_124, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_30, c_120])).
% 6.16/2.18  tff(c_147, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.16/2.18  tff(c_155, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_147])).
% 6.16/2.18  tff(c_2915, plain, (![A_17]: (A_17='#skF_4' | ~r1_tarski(A_17, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2912, c_2912, c_155])).
% 6.16/2.18  tff(c_3739, plain, (![D_478]: (k10_relat_1('#skF_4', D_478)='#skF_4')), inference(resolution, [status(thm)], [c_3689, c_2915])).
% 6.16/2.18  tff(c_3745, plain, (![A_439, B_440, D_442]: (k8_relset_1(A_439, B_440, '#skF_4', D_442)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3739, c_3346])).
% 6.16/2.18  tff(c_3848, plain, (![B_494, A_495, C_496]: (k8_relset_1(B_494, A_495, C_496, k7_relset_1(B_494, A_495, C_496, B_494))=k1_relset_1(B_494, A_495, C_496) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(B_494, A_495))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.16/2.18  tff(c_3856, plain, (![B_494, A_495]: (k8_relset_1(B_494, A_495, '#skF_4', k7_relset_1(B_494, A_495, '#skF_4', B_494))=k1_relset_1(B_494, A_495, '#skF_4'))), inference(resolution, [status(thm)], [c_2922, c_3848])).
% 6.16/2.18  tff(c_3862, plain, (![B_494, A_495]: (k1_relset_1(B_494, A_495, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3745, c_3856])).
% 6.16/2.18  tff(c_76, plain, (![B_52, A_51, C_53]: (k1_xboole_0=B_52 | k1_relset_1(A_51, B_52, C_53)=A_51 | ~v1_funct_2(C_53, A_51, B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.16/2.18  tff(c_3821, plain, (![B_490, A_491, C_492]: (B_490='#skF_4' | k1_relset_1(A_491, B_490, C_492)=A_491 | ~v1_funct_2(C_492, A_491, B_490) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(A_491, B_490))))), inference(demodulation, [status(thm), theory('equality')], [c_2912, c_76])).
% 6.16/2.18  tff(c_3838, plain, (![B_490, A_491]: (B_490='#skF_4' | k1_relset_1(A_491, B_490, '#skF_4')=A_491 | ~v1_funct_2('#skF_4', A_491, B_490))), inference(resolution, [status(thm)], [c_2922, c_3821])).
% 6.16/2.18  tff(c_5995, plain, (![B_671, A_672]: (B_671='#skF_4' | A_672='#skF_4' | ~v1_funct_2('#skF_4', A_672, B_671))), inference(demodulation, [status(thm), theory('equality')], [c_3862, c_3838])).
% 6.16/2.18  tff(c_6004, plain, ('#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_84, c_5995])).
% 6.16/2.18  tff(c_6012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3435, c_2924, c_6004])).
% 6.16/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.18  
% 6.16/2.18  Inference rules
% 6.16/2.18  ----------------------
% 6.16/2.18  #Ref     : 0
% 6.16/2.18  #Sup     : 1239
% 6.16/2.18  #Fact    : 1
% 6.16/2.18  #Define  : 0
% 6.16/2.18  #Split   : 12
% 6.16/2.18  #Chain   : 0
% 6.16/2.18  #Close   : 0
% 6.16/2.18  
% 6.16/2.18  Ordering : KBO
% 6.16/2.18  
% 6.16/2.18  Simplification rules
% 6.16/2.18  ----------------------
% 6.16/2.18  #Subsume      : 312
% 6.16/2.18  #Demod        : 893
% 6.16/2.18  #Tautology    : 438
% 6.16/2.18  #SimpNegUnit  : 11
% 6.16/2.18  #BackRed      : 32
% 6.16/2.18  
% 6.16/2.18  #Partial instantiations: 0
% 6.16/2.18  #Strategies tried      : 1
% 6.16/2.18  
% 6.16/2.18  Timing (in seconds)
% 6.16/2.18  ----------------------
% 6.16/2.18  Preprocessing        : 0.36
% 6.16/2.18  Parsing              : 0.19
% 6.16/2.18  CNF conversion       : 0.03
% 6.16/2.18  Main loop            : 1.07
% 6.16/2.18  Inferencing          : 0.38
% 6.16/2.18  Reduction            : 0.34
% 6.16/2.18  Demodulation         : 0.24
% 6.16/2.18  BG Simplification    : 0.04
% 6.16/2.19  Subsumption          : 0.22
% 6.16/2.19  Abstraction          : 0.05
% 6.16/2.19  MUC search           : 0.00
% 6.16/2.19  Cooper               : 0.00
% 6.16/2.19  Total                : 1.47
% 6.16/2.19  Index Insertion      : 0.00
% 6.16/2.19  Index Deletion       : 0.00
% 6.16/2.19  Index Matching       : 0.00
% 6.16/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
