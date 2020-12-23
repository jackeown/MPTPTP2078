%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:15 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  248 (1850 expanded)
%              Number of leaves         :   45 ( 584 expanded)
%              Depth                    :   19
%              Number of atoms          :  426 (4687 expanded)
%              Number of equality atoms :  164 (2002 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(A_57)
      | ~ v1_relat_1(B_58)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_131])).

tff(c_161,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_1329,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_137,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_131])).

tff(c_141,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_137])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_70,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2364,plain,(
    ! [C_391,A_392,B_393] :
      ( v2_funct_1(C_391)
      | ~ v3_funct_2(C_391,A_392,B_393)
      | ~ v1_funct_1(C_391)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2371,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2364])).

tff(c_2381,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2371])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2247,plain,(
    ! [A_371,B_372,C_373] :
      ( k1_relset_1(A_371,B_372,C_373) = k1_relat_1(C_373)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2262,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2247])).

tff(c_2974,plain,(
    ! [B_495,A_496,C_497] :
      ( k1_xboole_0 = B_495
      | k1_relset_1(A_496,B_495,C_497) = A_496
      | ~ v1_funct_2(C_497,A_496,B_495)
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(A_496,B_495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2981,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_2974])).

tff(c_2991,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2262,c_2981])).

tff(c_2993,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2991])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(B_20,k9_relat_1(B_20,A_19)) = A_19
      | ~ v2_funct_1(B_20)
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2997,plain,(
    ! [A_19] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_19)) = A_19
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2993,c_30])).

tff(c_3066,plain,(
    ! [A_501] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_501)) = A_501
      | ~ r1_tarski(A_501,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74,c_2381,c_2997])).

tff(c_2679,plain,(
    ! [A_440,B_441,C_442,D_443] :
      ( k7_relset_1(A_440,B_441,C_442,D_443) = k9_relat_1(C_442,D_443)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2690,plain,(
    ! [D_443] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_443) = k9_relat_1('#skF_3',D_443) ),
    inference(resolution,[status(thm)],[c_68,c_2679])).

tff(c_2294,plain,(
    ! [A_377,B_378,C_379,D_380] :
      ( k8_relset_1(A_377,B_378,C_379,D_380) = k10_relat_1(C_379,D_380)
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_377,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2305,plain,(
    ! [D_380] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_380) = k10_relat_1('#skF_3',D_380) ),
    inference(resolution,[status(thm)],[c_68,c_2294])).

tff(c_307,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_322,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_307])).

tff(c_448,plain,(
    ! [B_100,A_101] :
      ( k2_relat_1(B_100) = A_101
      | ~ v2_funct_2(B_100,A_101)
      | ~ v5_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_460,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_322,c_448])).

tff(c_470,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_460])).

tff(c_472,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_887,plain,(
    ! [C_180,B_181,A_182] :
      ( v2_funct_2(C_180,B_181)
      | ~ v3_funct_2(C_180,A_182,B_181)
      | ~ v1_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_894,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_887])).

tff(c_904,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_894])).

tff(c_906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_904])).

tff(c_907,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_1144,plain,(
    ! [B_217,A_218] :
      ( k9_relat_1(B_217,k10_relat_1(B_217,A_218)) = A_218
      | ~ r1_tarski(A_218,k2_relat_1(B_217))
      | ~ v1_funct_1(B_217)
      | ~ v1_relat_1(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1146,plain,(
    ! [A_218] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_218)) = A_218
      | ~ r1_tarski(A_218,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_1144])).

tff(c_1154,plain,(
    ! [A_218] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_218)) = A_218
      | ~ r1_tarski(A_218,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74,c_1146])).

tff(c_1298,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k7_relset_1(A_231,B_232,C_233,D_234) = k9_relat_1(C_233,D_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1309,plain,(
    ! [D_234] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_234) = k9_relat_1('#skF_3',D_234) ),
    inference(resolution,[status(thm)],[c_68,c_1298])).

tff(c_1038,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( k8_relset_1(A_198,B_199,C_200,D_201) = k10_relat_1(C_200,D_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1049,plain,(
    ! [D_201] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_201) = k10_relat_1('#skF_3',D_201) ),
    inference(resolution,[status(thm)],[c_68,c_1038])).

tff(c_64,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_162,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1050,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_162])).

tff(c_1310,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_1050])).

tff(c_1322,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_1310])).

tff(c_1326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1322])).

tff(c_1327,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2306,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2305,c_1327])).

tff(c_2691,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2690,c_2306])).

tff(c_3076,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3066,c_2691])).

tff(c_3111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3076])).

tff(c_3112,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2991])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_47,B_48] : v1_relat_1(k2_zfmisc_1(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_3160,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3112,c_106])).

tff(c_3165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1329,c_3160])).

tff(c_3167,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_5800,plain,(
    ! [C_882,A_883,B_884] :
      ( v2_funct_1(C_882)
      | ~ v3_funct_2(C_882,A_883,B_884)
      | ~ v1_funct_1(C_882)
      | ~ m1_subset_1(C_882,k1_zfmisc_1(k2_zfmisc_1(A_883,B_884))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5807,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5800])).

tff(c_5817,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_5807])).

tff(c_5588,plain,(
    ! [A_847,B_848,C_849] :
      ( k1_relset_1(A_847,B_848,C_849) = k1_relat_1(C_849)
      | ~ m1_subset_1(C_849,k1_zfmisc_1(k2_zfmisc_1(A_847,B_848))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5603,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5588])).

tff(c_6159,plain,(
    ! [B_940,A_941,C_942] :
      ( k1_xboole_0 = B_940
      | k1_relset_1(A_941,B_940,C_942) = A_941
      | ~ v1_funct_2(C_942,A_941,B_940)
      | ~ m1_subset_1(C_942,k1_zfmisc_1(k2_zfmisc_1(A_941,B_940))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6166,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_6159])).

tff(c_6176,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5603,c_6166])).

tff(c_6178,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6176])).

tff(c_6182,plain,(
    ! [A_19] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_19)) = A_19
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6178,c_30])).

tff(c_6251,plain,(
    ! [A_946] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_946)) = A_946
      | ~ r1_tarski(A_946,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74,c_5817,c_6182])).

tff(c_5892,plain,(
    ! [A_901,B_902,C_903,D_904] :
      ( k8_relset_1(A_901,B_902,C_903,D_904) = k10_relat_1(C_903,D_904)
      | ~ m1_subset_1(C_903,k1_zfmisc_1(k2_zfmisc_1(A_901,B_902))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5903,plain,(
    ! [D_904] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_904) = k10_relat_1('#skF_3',D_904) ),
    inference(resolution,[status(thm)],[c_68,c_5892])).

tff(c_5711,plain,(
    ! [A_866,B_867,C_868,D_869] :
      ( k7_relset_1(A_866,B_867,C_868,D_869) = k9_relat_1(C_868,D_869)
      | ~ m1_subset_1(C_868,k1_zfmisc_1(k2_zfmisc_1(A_866,B_867))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5722,plain,(
    ! [D_869] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_869) = k9_relat_1('#skF_3',D_869) ),
    inference(resolution,[status(thm)],[c_68,c_5711])).

tff(c_4029,plain,(
    ! [C_632,A_633,B_634] :
      ( v2_funct_1(C_632)
      | ~ v3_funct_2(C_632,A_633,B_634)
      | ~ v1_funct_1(C_632)
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4036,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4029])).

tff(c_4046,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_4036])).

tff(c_3942,plain,(
    ! [A_618,B_619,C_620] :
      ( k1_relset_1(A_618,B_619,C_620) = k1_relat_1(C_620)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3957,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3942])).

tff(c_4555,plain,(
    ! [B_715,A_716,C_717] :
      ( k1_xboole_0 = B_715
      | k1_relset_1(A_716,B_715,C_717) = A_716
      | ~ v1_funct_2(C_717,A_716,B_715)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(k2_zfmisc_1(A_716,B_715))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4562,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_4555])).

tff(c_4572,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3957,c_4562])).

tff(c_4574,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4572])).

tff(c_4578,plain,(
    ! [A_19] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_19)) = A_19
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4574,c_30])).

tff(c_4646,plain,(
    ! [A_719] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_719)) = A_719
      | ~ r1_tarski(A_719,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74,c_4046,c_4578])).

tff(c_4298,plain,(
    ! [A_677,B_678,C_679,D_680] :
      ( k8_relset_1(A_677,B_678,C_679,D_680) = k10_relat_1(C_679,D_680)
      | ~ m1_subset_1(C_679,k1_zfmisc_1(k2_zfmisc_1(A_677,B_678))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4309,plain,(
    ! [D_680] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_680) = k10_relat_1('#skF_3',D_680) ),
    inference(resolution,[status(thm)],[c_68,c_4298])).

tff(c_4141,plain,(
    ! [A_650,B_651,C_652,D_653] :
      ( k7_relset_1(A_650,B_651,C_652,D_653) = k9_relat_1(C_652,D_653)
      | ~ m1_subset_1(C_652,k1_zfmisc_1(k2_zfmisc_1(A_650,B_651))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4152,plain,(
    ! [D_653] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_653) = k9_relat_1('#skF_3',D_653) ),
    inference(resolution,[status(thm)],[c_68,c_4141])).

tff(c_4153,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4152,c_1327])).

tff(c_4311,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4309,c_4153])).

tff(c_4656,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4646,c_4311])).

tff(c_4691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4656])).

tff(c_4692,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4572])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4742,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4692,c_8])).

tff(c_3172,plain,(
    ! [B_502,A_503] :
      ( B_502 = A_503
      | ~ r1_tarski(B_502,A_503)
      | ~ r1_tarski(A_503,B_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3187,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_3172])).

tff(c_3201,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3187])).

tff(c_4750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4742,c_3201])).

tff(c_4751,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3187])).

tff(c_4784,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4751,c_4751,c_1327])).

tff(c_5732,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5722,c_4784])).

tff(c_5905,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5903,c_5732])).

tff(c_6261,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6251,c_5905])).

tff(c_6293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6261])).

tff(c_6294,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6176])).

tff(c_6346,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6294,c_8])).

tff(c_6344,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6294,c_6294,c_14])).

tff(c_110,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_110])).

tff(c_3181,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_3172])).

tff(c_4845,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3181])).

tff(c_6417,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6344,c_4845])).

tff(c_6422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6346,c_6417])).

tff(c_6423,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3181])).

tff(c_6426,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6423,c_68])).

tff(c_7778,plain,(
    ! [C_1146,A_1147,B_1148] :
      ( v2_funct_1(C_1146)
      | ~ v3_funct_2(C_1146,A_1147,B_1148)
      | ~ v1_funct_1(C_1146)
      | ~ m1_subset_1(C_1146,k1_zfmisc_1(k2_zfmisc_1(A_1147,B_1148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7793,plain,(
    ! [C_1149] :
      ( v2_funct_1(C_1149)
      | ~ v3_funct_2(C_1149,'#skF_1','#skF_1')
      | ~ v1_funct_1(C_1149)
      | ~ m1_subset_1(C_1149,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6423,c_7778])).

tff(c_7796,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6426,c_7793])).

tff(c_7803,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_7796])).

tff(c_7579,plain,(
    ! [A_1117,B_1118,C_1119] :
      ( k1_relset_1(A_1117,B_1118,C_1119) = k1_relat_1(C_1119)
      | ~ m1_subset_1(C_1119,k1_zfmisc_1(k2_zfmisc_1(A_1117,B_1118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7664,plain,(
    ! [C_1132] :
      ( k1_relset_1('#skF_1','#skF_1',C_1132) = k1_relat_1(C_1132)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6423,c_7579])).

tff(c_7672,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6426,c_7664])).

tff(c_8233,plain,(
    ! [B_1229,A_1230,C_1231] :
      ( k1_xboole_0 = B_1229
      | k1_relset_1(A_1230,B_1229,C_1231) = A_1230
      | ~ v1_funct_2(C_1231,A_1230,B_1229)
      | ~ m1_subset_1(C_1231,k1_zfmisc_1(k2_zfmisc_1(A_1230,B_1229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8236,plain,(
    ! [C_1231] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1('#skF_1','#skF_1',C_1231) = '#skF_1'
      | ~ v1_funct_2(C_1231,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1231,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6423,c_8233])).

tff(c_8297,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8236])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6443,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6423,c_10])).

tff(c_6468,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6443])).

tff(c_8342,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8297,c_6468])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8350,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8297,c_8297,c_12])).

tff(c_8480,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8350,c_6423])).

tff(c_8482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8342,c_8480])).

tff(c_8551,plain,(
    ! [C_1263] :
      ( k1_relset_1('#skF_1','#skF_1',C_1263) = '#skF_1'
      | ~ v1_funct_2(C_1263,'#skF_1','#skF_1')
      | ~ m1_subset_1(C_1263,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_8236])).

tff(c_8554,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_6426,c_8551])).

tff(c_8561,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7672,c_8554])).

tff(c_8566,plain,(
    ! [A_19] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_19)) = A_19
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8561,c_30])).

tff(c_8634,plain,(
    ! [A_1265] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_1265)) = A_1265
      | ~ r1_tarski(A_1265,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74,c_7803,c_8566])).

tff(c_7935,plain,(
    ! [A_1176,B_1177,C_1178,D_1179] :
      ( k7_relset_1(A_1176,B_1177,C_1178,D_1179) = k9_relat_1(C_1178,D_1179)
      | ~ m1_subset_1(C_1178,k1_zfmisc_1(k2_zfmisc_1(A_1176,B_1177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8069,plain,(
    ! [C_1200,D_1201] :
      ( k7_relset_1('#skF_1','#skF_1',C_1200,D_1201) = k9_relat_1(C_1200,D_1201)
      | ~ m1_subset_1(C_1200,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6423,c_7935])).

tff(c_8075,plain,(
    ! [D_1201] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_1201) = k9_relat_1('#skF_3',D_1201) ),
    inference(resolution,[status(thm)],[c_6426,c_8069])).

tff(c_7834,plain,(
    ! [A_1158,B_1159,C_1160,D_1161] :
      ( k8_relset_1(A_1158,B_1159,C_1160,D_1161) = k10_relat_1(C_1160,D_1161)
      | ~ m1_subset_1(C_1160,k1_zfmisc_1(k2_zfmisc_1(A_1158,B_1159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7847,plain,(
    ! [C_1164,D_1165] :
      ( k8_relset_1('#skF_1','#skF_1',C_1164,D_1165) = k10_relat_1(C_1164,D_1165)
      | ~ m1_subset_1(C_1164,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6423,c_7834])).

tff(c_7853,plain,(
    ! [D_1165] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_1165) = k10_relat_1('#skF_3',D_1165) ),
    inference(resolution,[status(thm)],[c_6426,c_7847])).

tff(c_7856,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7853,c_4784])).

tff(c_8077,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8075,c_7856])).

tff(c_8644,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8634,c_8077])).

tff(c_8676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8644])).

tff(c_8678,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6443])).

tff(c_8677,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6443])).

tff(c_8778,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8678,c_8678,c_8677])).

tff(c_8779,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_8778])).

tff(c_8797,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_74])).

tff(c_8789,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_8779,c_6426])).

tff(c_8795,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_70])).

tff(c_8686,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8678,c_8678,c_12])).

tff(c_8782,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_8779,c_8686])).

tff(c_9298,plain,(
    ! [C_1330,A_1331,B_1332] :
      ( v2_funct_1(C_1330)
      | ~ v3_funct_2(C_1330,A_1331,B_1332)
      | ~ v1_funct_1(C_1330)
      | ~ m1_subset_1(C_1330,k1_zfmisc_1(k2_zfmisc_1(A_1331,B_1332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_9465,plain,(
    ! [C_1358,A_1359] :
      ( v2_funct_1(C_1358)
      | ~ v3_funct_2(C_1358,A_1359,'#skF_1')
      | ~ v1_funct_1(C_1358)
      | ~ m1_subset_1(C_1358,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8782,c_9298])).

tff(c_9467,plain,
    ( v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_8795,c_9465])).

tff(c_9470,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8789,c_8797,c_9467])).

tff(c_8786,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_8678])).

tff(c_4819,plain,(
    ! [C_735,A_736,B_737] :
      ( v4_relat_1(C_735,A_736)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k2_zfmisc_1(A_736,B_737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4832,plain,(
    ! [C_735,A_4] :
      ( v4_relat_1(C_735,A_4)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4819])).

tff(c_8989,plain,(
    ! [C_1288,A_1289] :
      ( v4_relat_1(C_1288,A_1289)
      | ~ m1_subset_1(C_1288,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8786,c_4832])).

tff(c_9010,plain,(
    ! [A_1293] : v4_relat_1('#skF_1',A_1293) ),
    inference(resolution,[status(thm)],[c_8789,c_8989])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_9013,plain,(
    ! [A_1293] :
      ( k7_relat_1('#skF_1',A_1293) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_9010,c_24])).

tff(c_9016,plain,(
    ! [A_1293] : k7_relat_1('#skF_1',A_1293) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3167,c_9013])).

tff(c_8687,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8678,c_8])).

tff(c_8783,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_8687])).

tff(c_8948,plain,(
    ! [B_1283,A_1284] :
      ( k1_relat_1(k7_relat_1(B_1283,A_1284)) = A_1284
      | ~ r1_tarski(A_1284,k1_relat_1(B_1283))
      | ~ v1_relat_1(B_1283) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9068,plain,(
    ! [B_1305] :
      ( k1_relat_1(k7_relat_1(B_1305,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1305) ) ),
    inference(resolution,[status(thm)],[c_8783,c_8948])).

tff(c_9081,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9016,c_9068])).

tff(c_9085,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3167,c_9081])).

tff(c_9551,plain,(
    ! [B_1378,A_1379] :
      ( k10_relat_1(B_1378,k9_relat_1(B_1378,A_1379)) = A_1379
      | ~ v2_funct_1(B_1378)
      | ~ r1_tarski(A_1379,k1_relat_1(B_1378))
      | ~ v1_funct_1(B_1378)
      | ~ v1_relat_1(B_1378) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9555,plain,(
    ! [A_1379] :
      ( k10_relat_1('#skF_1',k9_relat_1('#skF_1',A_1379)) = A_1379
      | ~ v2_funct_1('#skF_1')
      | ~ r1_tarski(A_1379,'#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9085,c_9551])).

tff(c_9596,plain,(
    ! [A_1380] :
      ( k10_relat_1('#skF_1',k9_relat_1('#skF_1',A_1380)) = A_1380
      | ~ r1_tarski(A_1380,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3167,c_8797,c_9470,c_9555])).

tff(c_9059,plain,(
    ! [A_1301,B_1302,C_1303,D_1304] :
      ( k8_relset_1(A_1301,B_1302,C_1303,D_1304) = k10_relat_1(C_1303,D_1304)
      | ~ m1_subset_1(C_1303,k1_zfmisc_1(k2_zfmisc_1(A_1301,B_1302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9531,plain,(
    ! [A_1373,C_1374,D_1375] :
      ( k8_relset_1(A_1373,'#skF_1',C_1374,D_1375) = k10_relat_1(C_1374,D_1375)
      | ~ m1_subset_1(C_1374,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8782,c_9059])).

tff(c_9537,plain,(
    ! [A_1373,D_1375] : k8_relset_1(A_1373,'#skF_1','#skF_1',D_1375) = k10_relat_1('#skF_1',D_1375) ),
    inference(resolution,[status(thm)],[c_8789,c_9531])).

tff(c_8685,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8678,c_8678,c_14])).

tff(c_8781,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_8779,c_8685])).

tff(c_9417,plain,(
    ! [A_1349,B_1350,C_1351,D_1352] :
      ( k7_relset_1(A_1349,B_1350,C_1351,D_1352) = k9_relat_1(C_1351,D_1352)
      | ~ m1_subset_1(C_1351,k1_zfmisc_1(k2_zfmisc_1(A_1349,B_1350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9491,plain,(
    ! [B_1365,C_1366,D_1367] :
      ( k7_relset_1('#skF_1',B_1365,C_1366,D_1367) = k9_relat_1(C_1366,D_1367)
      | ~ m1_subset_1(C_1366,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8781,c_9417])).

tff(c_9497,plain,(
    ! [B_1365,D_1367] : k7_relset_1('#skF_1',B_1365,'#skF_1',D_1367) = k9_relat_1('#skF_1',D_1367) ),
    inference(resolution,[status(thm)],[c_8789,c_9491])).

tff(c_8793,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_1',k7_relset_1('#skF_1','#skF_1','#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8779,c_8779,c_4784])).

tff(c_9499,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_1',k9_relat_1('#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9497,c_8793])).

tff(c_9540,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9537,c_9499])).

tff(c_9602,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9596,c_9540])).

tff(c_9621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9602])).

tff(c_9622,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8778])).

tff(c_9623,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8778])).

tff(c_9648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9622,c_9623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.75  
% 7.74/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.75  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.74/2.75  
% 7.74/2.75  %Foreground sorts:
% 7.74/2.75  
% 7.74/2.75  
% 7.74/2.75  %Background operators:
% 7.74/2.75  
% 7.74/2.75  
% 7.74/2.75  %Foreground operators:
% 7.74/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.74/2.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.74/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/2.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.74/2.75  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.74/2.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.74/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.74/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.74/2.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.74/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.74/2.75  tff('#skF_2', type, '#skF_2': $i).
% 7.74/2.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.74/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.74/2.75  tff('#skF_1', type, '#skF_1': $i).
% 7.74/2.76  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.74/2.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.74/2.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.74/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.74/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/2.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.74/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.74/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.74/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/2.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.74/2.76  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 7.74/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.74/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.74/2.76  
% 7.74/2.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.74/2.79  tff(f_153, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 7.74/2.79  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.74/2.79  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.74/2.79  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.74/2.79  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 7.74/2.79  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.74/2.79  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.74/2.79  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 7.74/2.79  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.74/2.79  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.74/2.79  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.74/2.79  tff(f_138, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.74/2.79  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 7.74/2.79  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.74/2.79  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.74/2.79  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 7.74/2.79  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.74/2.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.74/2.79  tff(c_66, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.74/2.79  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.74/2.79  tff(c_131, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.74/2.79  tff(c_142, plain, (![A_57, B_58]: (v1_relat_1(A_57) | ~v1_relat_1(B_58) | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_18, c_131])).
% 7.74/2.79  tff(c_161, plain, (v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_66, c_142])).
% 7.74/2.79  tff(c_1329, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_161])).
% 7.74/2.79  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.79  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.74/2.79  tff(c_137, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_131])).
% 7.74/2.79  tff(c_141, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_137])).
% 7.74/2.79  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.74/2.79  tff(c_70, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.74/2.79  tff(c_2364, plain, (![C_391, A_392, B_393]: (v2_funct_1(C_391) | ~v3_funct_2(C_391, A_392, B_393) | ~v1_funct_1(C_391) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.74/2.79  tff(c_2371, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2364])).
% 7.74/2.79  tff(c_2381, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2371])).
% 7.74/2.79  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.74/2.79  tff(c_2247, plain, (![A_371, B_372, C_373]: (k1_relset_1(A_371, B_372, C_373)=k1_relat_1(C_373) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.74/2.79  tff(c_2262, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2247])).
% 7.74/2.79  tff(c_2974, plain, (![B_495, A_496, C_497]: (k1_xboole_0=B_495 | k1_relset_1(A_496, B_495, C_497)=A_496 | ~v1_funct_2(C_497, A_496, B_495) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(A_496, B_495))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.79  tff(c_2981, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_2974])).
% 7.74/2.79  tff(c_2991, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2262, c_2981])).
% 7.74/2.79  tff(c_2993, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2991])).
% 7.74/2.79  tff(c_30, plain, (![B_20, A_19]: (k10_relat_1(B_20, k9_relat_1(B_20, A_19))=A_19 | ~v2_funct_1(B_20) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.74/2.79  tff(c_2997, plain, (![A_19]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_19))=A_19 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_19, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2993, c_30])).
% 7.74/2.79  tff(c_3066, plain, (![A_501]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_501))=A_501 | ~r1_tarski(A_501, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74, c_2381, c_2997])).
% 7.74/2.79  tff(c_2679, plain, (![A_440, B_441, C_442, D_443]: (k7_relset_1(A_440, B_441, C_442, D_443)=k9_relat_1(C_442, D_443) | ~m1_subset_1(C_442, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.74/2.79  tff(c_2690, plain, (![D_443]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_443)=k9_relat_1('#skF_3', D_443))), inference(resolution, [status(thm)], [c_68, c_2679])).
% 7.74/2.79  tff(c_2294, plain, (![A_377, B_378, C_379, D_380]: (k8_relset_1(A_377, B_378, C_379, D_380)=k10_relat_1(C_379, D_380) | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_377, B_378))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.79  tff(c_2305, plain, (![D_380]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_380)=k10_relat_1('#skF_3', D_380))), inference(resolution, [status(thm)], [c_68, c_2294])).
% 7.74/2.79  tff(c_307, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.74/2.79  tff(c_322, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_307])).
% 7.74/2.79  tff(c_448, plain, (![B_100, A_101]: (k2_relat_1(B_100)=A_101 | ~v2_funct_2(B_100, A_101) | ~v5_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.74/2.79  tff(c_460, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_322, c_448])).
% 7.74/2.79  tff(c_470, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_460])).
% 7.74/2.79  tff(c_472, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_470])).
% 7.74/2.79  tff(c_887, plain, (![C_180, B_181, A_182]: (v2_funct_2(C_180, B_181) | ~v3_funct_2(C_180, A_182, B_181) | ~v1_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.74/2.79  tff(c_894, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_887])).
% 7.74/2.79  tff(c_904, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_894])).
% 7.74/2.79  tff(c_906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_904])).
% 7.74/2.79  tff(c_907, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_470])).
% 7.74/2.79  tff(c_1144, plain, (![B_217, A_218]: (k9_relat_1(B_217, k10_relat_1(B_217, A_218))=A_218 | ~r1_tarski(A_218, k2_relat_1(B_217)) | ~v1_funct_1(B_217) | ~v1_relat_1(B_217))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.74/2.79  tff(c_1146, plain, (![A_218]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_218))=A_218 | ~r1_tarski(A_218, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_907, c_1144])).
% 7.74/2.79  tff(c_1154, plain, (![A_218]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_218))=A_218 | ~r1_tarski(A_218, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74, c_1146])).
% 7.74/2.79  tff(c_1298, plain, (![A_231, B_232, C_233, D_234]: (k7_relset_1(A_231, B_232, C_233, D_234)=k9_relat_1(C_233, D_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.74/2.79  tff(c_1309, plain, (![D_234]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_234)=k9_relat_1('#skF_3', D_234))), inference(resolution, [status(thm)], [c_68, c_1298])).
% 7.74/2.79  tff(c_1038, plain, (![A_198, B_199, C_200, D_201]: (k8_relset_1(A_198, B_199, C_200, D_201)=k10_relat_1(C_200, D_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.79  tff(c_1049, plain, (![D_201]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_201)=k10_relat_1('#skF_3', D_201))), inference(resolution, [status(thm)], [c_68, c_1038])).
% 7.74/2.79  tff(c_64, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 7.74/2.79  tff(c_162, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 7.74/2.79  tff(c_1050, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_162])).
% 7.74/2.79  tff(c_1310, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_1050])).
% 7.74/2.79  tff(c_1322, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1154, c_1310])).
% 7.74/2.79  tff(c_1326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1322])).
% 7.74/2.79  tff(c_1327, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 7.74/2.79  tff(c_2306, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2305, c_1327])).
% 7.74/2.79  tff(c_2691, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2690, c_2306])).
% 7.74/2.79  tff(c_3076, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3066, c_2691])).
% 7.74/2.79  tff(c_3111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3076])).
% 7.74/2.79  tff(c_3112, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2991])).
% 7.74/2.79  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.74/2.79  tff(c_104, plain, (![A_47, B_48]: (v1_relat_1(k2_zfmisc_1(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.74/2.79  tff(c_106, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_104])).
% 7.74/2.79  tff(c_3160, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3112, c_106])).
% 7.74/2.79  tff(c_3165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1329, c_3160])).
% 7.74/2.79  tff(c_3167, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_161])).
% 7.74/2.79  tff(c_5800, plain, (![C_882, A_883, B_884]: (v2_funct_1(C_882) | ~v3_funct_2(C_882, A_883, B_884) | ~v1_funct_1(C_882) | ~m1_subset_1(C_882, k1_zfmisc_1(k2_zfmisc_1(A_883, B_884))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.74/2.79  tff(c_5807, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5800])).
% 7.74/2.79  tff(c_5817, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_5807])).
% 7.74/2.79  tff(c_5588, plain, (![A_847, B_848, C_849]: (k1_relset_1(A_847, B_848, C_849)=k1_relat_1(C_849) | ~m1_subset_1(C_849, k1_zfmisc_1(k2_zfmisc_1(A_847, B_848))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.74/2.79  tff(c_5603, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5588])).
% 7.74/2.79  tff(c_6159, plain, (![B_940, A_941, C_942]: (k1_xboole_0=B_940 | k1_relset_1(A_941, B_940, C_942)=A_941 | ~v1_funct_2(C_942, A_941, B_940) | ~m1_subset_1(C_942, k1_zfmisc_1(k2_zfmisc_1(A_941, B_940))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.79  tff(c_6166, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_6159])).
% 7.74/2.79  tff(c_6176, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5603, c_6166])).
% 7.74/2.79  tff(c_6178, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_6176])).
% 7.74/2.79  tff(c_6182, plain, (![A_19]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_19))=A_19 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_19, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6178, c_30])).
% 7.74/2.79  tff(c_6251, plain, (![A_946]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_946))=A_946 | ~r1_tarski(A_946, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74, c_5817, c_6182])).
% 7.74/2.79  tff(c_5892, plain, (![A_901, B_902, C_903, D_904]: (k8_relset_1(A_901, B_902, C_903, D_904)=k10_relat_1(C_903, D_904) | ~m1_subset_1(C_903, k1_zfmisc_1(k2_zfmisc_1(A_901, B_902))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.79  tff(c_5903, plain, (![D_904]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_904)=k10_relat_1('#skF_3', D_904))), inference(resolution, [status(thm)], [c_68, c_5892])).
% 7.74/2.79  tff(c_5711, plain, (![A_866, B_867, C_868, D_869]: (k7_relset_1(A_866, B_867, C_868, D_869)=k9_relat_1(C_868, D_869) | ~m1_subset_1(C_868, k1_zfmisc_1(k2_zfmisc_1(A_866, B_867))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.74/2.79  tff(c_5722, plain, (![D_869]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_869)=k9_relat_1('#skF_3', D_869))), inference(resolution, [status(thm)], [c_68, c_5711])).
% 7.74/2.79  tff(c_4029, plain, (![C_632, A_633, B_634]: (v2_funct_1(C_632) | ~v3_funct_2(C_632, A_633, B_634) | ~v1_funct_1(C_632) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.74/2.79  tff(c_4036, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4029])).
% 7.74/2.79  tff(c_4046, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_4036])).
% 7.74/2.79  tff(c_3942, plain, (![A_618, B_619, C_620]: (k1_relset_1(A_618, B_619, C_620)=k1_relat_1(C_620) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.74/2.79  tff(c_3957, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3942])).
% 7.74/2.79  tff(c_4555, plain, (![B_715, A_716, C_717]: (k1_xboole_0=B_715 | k1_relset_1(A_716, B_715, C_717)=A_716 | ~v1_funct_2(C_717, A_716, B_715) | ~m1_subset_1(C_717, k1_zfmisc_1(k2_zfmisc_1(A_716, B_715))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.79  tff(c_4562, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_4555])).
% 7.74/2.79  tff(c_4572, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3957, c_4562])).
% 7.74/2.79  tff(c_4574, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4572])).
% 7.74/2.79  tff(c_4578, plain, (![A_19]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_19))=A_19 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_19, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4574, c_30])).
% 7.74/2.79  tff(c_4646, plain, (![A_719]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_719))=A_719 | ~r1_tarski(A_719, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74, c_4046, c_4578])).
% 7.74/2.79  tff(c_4298, plain, (![A_677, B_678, C_679, D_680]: (k8_relset_1(A_677, B_678, C_679, D_680)=k10_relat_1(C_679, D_680) | ~m1_subset_1(C_679, k1_zfmisc_1(k2_zfmisc_1(A_677, B_678))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.79  tff(c_4309, plain, (![D_680]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_680)=k10_relat_1('#skF_3', D_680))), inference(resolution, [status(thm)], [c_68, c_4298])).
% 7.74/2.79  tff(c_4141, plain, (![A_650, B_651, C_652, D_653]: (k7_relset_1(A_650, B_651, C_652, D_653)=k9_relat_1(C_652, D_653) | ~m1_subset_1(C_652, k1_zfmisc_1(k2_zfmisc_1(A_650, B_651))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.74/2.79  tff(c_4152, plain, (![D_653]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_653)=k9_relat_1('#skF_3', D_653))), inference(resolution, [status(thm)], [c_68, c_4141])).
% 7.74/2.79  tff(c_4153, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4152, c_1327])).
% 7.74/2.79  tff(c_4311, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4309, c_4153])).
% 7.74/2.79  tff(c_4656, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4646, c_4311])).
% 7.74/2.79  tff(c_4691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_4656])).
% 7.74/2.79  tff(c_4692, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4572])).
% 7.74/2.79  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.74/2.79  tff(c_4742, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4692, c_8])).
% 7.74/2.79  tff(c_3172, plain, (![B_502, A_503]: (B_502=A_503 | ~r1_tarski(B_502, A_503) | ~r1_tarski(A_503, B_502))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.74/2.79  tff(c_3187, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_3172])).
% 7.74/2.79  tff(c_3201, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_3187])).
% 7.74/2.79  tff(c_4750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4742, c_3201])).
% 7.74/2.79  tff(c_4751, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_3187])).
% 7.74/2.79  tff(c_4784, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4751, c_4751, c_1327])).
% 7.74/2.79  tff(c_5732, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5722, c_4784])).
% 7.74/2.79  tff(c_5905, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5903, c_5732])).
% 7.74/2.79  tff(c_6261, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6251, c_5905])).
% 7.74/2.79  tff(c_6293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6261])).
% 7.74/2.79  tff(c_6294, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6176])).
% 7.74/2.79  tff(c_6346, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6294, c_8])).
% 7.74/2.79  tff(c_6344, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6294, c_6294, c_14])).
% 7.74/2.79  tff(c_110, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.74/2.79  tff(c_114, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_110])).
% 7.74/2.79  tff(c_3181, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_114, c_3172])).
% 7.74/2.79  tff(c_4845, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3181])).
% 7.74/2.79  tff(c_6417, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6344, c_4845])).
% 7.74/2.79  tff(c_6422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6346, c_6417])).
% 7.74/2.79  tff(c_6423, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_3181])).
% 7.74/2.79  tff(c_6426, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6423, c_68])).
% 7.74/2.79  tff(c_7778, plain, (![C_1146, A_1147, B_1148]: (v2_funct_1(C_1146) | ~v3_funct_2(C_1146, A_1147, B_1148) | ~v1_funct_1(C_1146) | ~m1_subset_1(C_1146, k1_zfmisc_1(k2_zfmisc_1(A_1147, B_1148))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.74/2.79  tff(c_7793, plain, (![C_1149]: (v2_funct_1(C_1149) | ~v3_funct_2(C_1149, '#skF_1', '#skF_1') | ~v1_funct_1(C_1149) | ~m1_subset_1(C_1149, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6423, c_7778])).
% 7.74/2.79  tff(c_7796, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6426, c_7793])).
% 7.74/2.79  tff(c_7803, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_7796])).
% 7.74/2.79  tff(c_7579, plain, (![A_1117, B_1118, C_1119]: (k1_relset_1(A_1117, B_1118, C_1119)=k1_relat_1(C_1119) | ~m1_subset_1(C_1119, k1_zfmisc_1(k2_zfmisc_1(A_1117, B_1118))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.74/2.79  tff(c_7664, plain, (![C_1132]: (k1_relset_1('#skF_1', '#skF_1', C_1132)=k1_relat_1(C_1132) | ~m1_subset_1(C_1132, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6423, c_7579])).
% 7.74/2.79  tff(c_7672, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6426, c_7664])).
% 7.74/2.79  tff(c_8233, plain, (![B_1229, A_1230, C_1231]: (k1_xboole_0=B_1229 | k1_relset_1(A_1230, B_1229, C_1231)=A_1230 | ~v1_funct_2(C_1231, A_1230, B_1229) | ~m1_subset_1(C_1231, k1_zfmisc_1(k2_zfmisc_1(A_1230, B_1229))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.74/2.79  tff(c_8236, plain, (![C_1231]: (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', C_1231)='#skF_1' | ~v1_funct_2(C_1231, '#skF_1', '#skF_1') | ~m1_subset_1(C_1231, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6423, c_8233])).
% 7.74/2.79  tff(c_8297, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_8236])).
% 7.74/2.79  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.74/2.79  tff(c_6443, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6423, c_10])).
% 7.74/2.79  tff(c_6468, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_6443])).
% 7.74/2.79  tff(c_8342, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8297, c_6468])).
% 7.74/2.79  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.74/2.79  tff(c_8350, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8297, c_8297, c_12])).
% 7.74/2.79  tff(c_8480, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8350, c_6423])).
% 7.74/2.79  tff(c_8482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8342, c_8480])).
% 7.74/2.79  tff(c_8551, plain, (![C_1263]: (k1_relset_1('#skF_1', '#skF_1', C_1263)='#skF_1' | ~v1_funct_2(C_1263, '#skF_1', '#skF_1') | ~m1_subset_1(C_1263, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_8236])).
% 7.74/2.79  tff(c_8554, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_6426, c_8551])).
% 7.74/2.79  tff(c_8561, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7672, c_8554])).
% 7.74/2.79  tff(c_8566, plain, (![A_19]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_19))=A_19 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_19, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8561, c_30])).
% 7.74/2.79  tff(c_8634, plain, (![A_1265]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_1265))=A_1265 | ~r1_tarski(A_1265, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74, c_7803, c_8566])).
% 7.74/2.79  tff(c_7935, plain, (![A_1176, B_1177, C_1178, D_1179]: (k7_relset_1(A_1176, B_1177, C_1178, D_1179)=k9_relat_1(C_1178, D_1179) | ~m1_subset_1(C_1178, k1_zfmisc_1(k2_zfmisc_1(A_1176, B_1177))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.74/2.79  tff(c_8069, plain, (![C_1200, D_1201]: (k7_relset_1('#skF_1', '#skF_1', C_1200, D_1201)=k9_relat_1(C_1200, D_1201) | ~m1_subset_1(C_1200, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6423, c_7935])).
% 7.74/2.79  tff(c_8075, plain, (![D_1201]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_1201)=k9_relat_1('#skF_3', D_1201))), inference(resolution, [status(thm)], [c_6426, c_8069])).
% 7.74/2.79  tff(c_7834, plain, (![A_1158, B_1159, C_1160, D_1161]: (k8_relset_1(A_1158, B_1159, C_1160, D_1161)=k10_relat_1(C_1160, D_1161) | ~m1_subset_1(C_1160, k1_zfmisc_1(k2_zfmisc_1(A_1158, B_1159))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.79  tff(c_7847, plain, (![C_1164, D_1165]: (k8_relset_1('#skF_1', '#skF_1', C_1164, D_1165)=k10_relat_1(C_1164, D_1165) | ~m1_subset_1(C_1164, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6423, c_7834])).
% 7.74/2.79  tff(c_7853, plain, (![D_1165]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_1165)=k10_relat_1('#skF_3', D_1165))), inference(resolution, [status(thm)], [c_6426, c_7847])).
% 7.74/2.79  tff(c_7856, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7853, c_4784])).
% 7.74/2.79  tff(c_8077, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8075, c_7856])).
% 7.74/2.79  tff(c_8644, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8634, c_8077])).
% 7.74/2.79  tff(c_8676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8644])).
% 7.74/2.79  tff(c_8678, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6443])).
% 7.74/2.79  tff(c_8677, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_6443])).
% 7.74/2.79  tff(c_8778, plain, ('#skF_3'='#skF_1' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8678, c_8678, c_8677])).
% 7.74/2.79  tff(c_8779, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_8778])).
% 7.74/2.79  tff(c_8797, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_74])).
% 7.74/2.79  tff(c_8789, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_8779, c_6426])).
% 7.74/2.79  tff(c_8795, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_70])).
% 7.74/2.79  tff(c_8686, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8678, c_8678, c_12])).
% 7.74/2.79  tff(c_8782, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_8779, c_8686])).
% 7.74/2.79  tff(c_9298, plain, (![C_1330, A_1331, B_1332]: (v2_funct_1(C_1330) | ~v3_funct_2(C_1330, A_1331, B_1332) | ~v1_funct_1(C_1330) | ~m1_subset_1(C_1330, k1_zfmisc_1(k2_zfmisc_1(A_1331, B_1332))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.74/2.79  tff(c_9465, plain, (![C_1358, A_1359]: (v2_funct_1(C_1358) | ~v3_funct_2(C_1358, A_1359, '#skF_1') | ~v1_funct_1(C_1358) | ~m1_subset_1(C_1358, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8782, c_9298])).
% 7.74/2.79  tff(c_9467, plain, (v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_8795, c_9465])).
% 7.74/2.79  tff(c_9470, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8789, c_8797, c_9467])).
% 7.74/2.79  tff(c_8786, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_8678])).
% 7.74/2.79  tff(c_4819, plain, (![C_735, A_736, B_737]: (v4_relat_1(C_735, A_736) | ~m1_subset_1(C_735, k1_zfmisc_1(k2_zfmisc_1(A_736, B_737))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.74/2.79  tff(c_4832, plain, (![C_735, A_4]: (v4_relat_1(C_735, A_4) | ~m1_subset_1(C_735, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4819])).
% 7.74/2.79  tff(c_8989, plain, (![C_1288, A_1289]: (v4_relat_1(C_1288, A_1289) | ~m1_subset_1(C_1288, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8786, c_4832])).
% 7.74/2.79  tff(c_9010, plain, (![A_1293]: (v4_relat_1('#skF_1', A_1293))), inference(resolution, [status(thm)], [c_8789, c_8989])).
% 7.74/2.79  tff(c_24, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.74/2.79  tff(c_9013, plain, (![A_1293]: (k7_relat_1('#skF_1', A_1293)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_9010, c_24])).
% 7.74/2.79  tff(c_9016, plain, (![A_1293]: (k7_relat_1('#skF_1', A_1293)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3167, c_9013])).
% 7.74/2.79  tff(c_8687, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8678, c_8])).
% 7.74/2.79  tff(c_8783, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_8687])).
% 7.74/2.79  tff(c_8948, plain, (![B_1283, A_1284]: (k1_relat_1(k7_relat_1(B_1283, A_1284))=A_1284 | ~r1_tarski(A_1284, k1_relat_1(B_1283)) | ~v1_relat_1(B_1283))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.74/2.79  tff(c_9068, plain, (![B_1305]: (k1_relat_1(k7_relat_1(B_1305, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1305))), inference(resolution, [status(thm)], [c_8783, c_8948])).
% 7.74/2.79  tff(c_9081, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9016, c_9068])).
% 7.74/2.79  tff(c_9085, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3167, c_9081])).
% 7.74/2.79  tff(c_9551, plain, (![B_1378, A_1379]: (k10_relat_1(B_1378, k9_relat_1(B_1378, A_1379))=A_1379 | ~v2_funct_1(B_1378) | ~r1_tarski(A_1379, k1_relat_1(B_1378)) | ~v1_funct_1(B_1378) | ~v1_relat_1(B_1378))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.74/2.79  tff(c_9555, plain, (![A_1379]: (k10_relat_1('#skF_1', k9_relat_1('#skF_1', A_1379))=A_1379 | ~v2_funct_1('#skF_1') | ~r1_tarski(A_1379, '#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9085, c_9551])).
% 7.74/2.79  tff(c_9596, plain, (![A_1380]: (k10_relat_1('#skF_1', k9_relat_1('#skF_1', A_1380))=A_1380 | ~r1_tarski(A_1380, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3167, c_8797, c_9470, c_9555])).
% 7.74/2.79  tff(c_9059, plain, (![A_1301, B_1302, C_1303, D_1304]: (k8_relset_1(A_1301, B_1302, C_1303, D_1304)=k10_relat_1(C_1303, D_1304) | ~m1_subset_1(C_1303, k1_zfmisc_1(k2_zfmisc_1(A_1301, B_1302))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.74/2.79  tff(c_9531, plain, (![A_1373, C_1374, D_1375]: (k8_relset_1(A_1373, '#skF_1', C_1374, D_1375)=k10_relat_1(C_1374, D_1375) | ~m1_subset_1(C_1374, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8782, c_9059])).
% 7.74/2.79  tff(c_9537, plain, (![A_1373, D_1375]: (k8_relset_1(A_1373, '#skF_1', '#skF_1', D_1375)=k10_relat_1('#skF_1', D_1375))), inference(resolution, [status(thm)], [c_8789, c_9531])).
% 7.74/2.79  tff(c_8685, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8678, c_8678, c_14])).
% 7.74/2.79  tff(c_8781, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_8779, c_8685])).
% 7.74/2.79  tff(c_9417, plain, (![A_1349, B_1350, C_1351, D_1352]: (k7_relset_1(A_1349, B_1350, C_1351, D_1352)=k9_relat_1(C_1351, D_1352) | ~m1_subset_1(C_1351, k1_zfmisc_1(k2_zfmisc_1(A_1349, B_1350))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.74/2.79  tff(c_9491, plain, (![B_1365, C_1366, D_1367]: (k7_relset_1('#skF_1', B_1365, C_1366, D_1367)=k9_relat_1(C_1366, D_1367) | ~m1_subset_1(C_1366, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8781, c_9417])).
% 7.74/2.79  tff(c_9497, plain, (![B_1365, D_1367]: (k7_relset_1('#skF_1', B_1365, '#skF_1', D_1367)=k9_relat_1('#skF_1', D_1367))), inference(resolution, [status(thm)], [c_8789, c_9491])).
% 7.74/2.79  tff(c_8793, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_1', k7_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8779, c_8779, c_4784])).
% 7.74/2.79  tff(c_9499, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_1', k9_relat_1('#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9497, c_8793])).
% 7.74/2.79  tff(c_9540, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9537, c_9499])).
% 7.74/2.79  tff(c_9602, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9596, c_9540])).
% 7.74/2.79  tff(c_9621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9602])).
% 7.74/2.79  tff(c_9622, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_8778])).
% 7.74/2.79  tff(c_9623, plain, ('#skF_3'!='#skF_1'), inference(splitRight, [status(thm)], [c_8778])).
% 7.74/2.79  tff(c_9648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9622, c_9623])).
% 7.74/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.79  
% 7.74/2.79  Inference rules
% 7.74/2.79  ----------------------
% 7.74/2.79  #Ref     : 0
% 7.74/2.79  #Sup     : 2055
% 7.74/2.79  #Fact    : 0
% 7.74/2.79  #Define  : 0
% 7.74/2.79  #Split   : 29
% 7.74/2.79  #Chain   : 0
% 7.74/2.79  #Close   : 0
% 7.74/2.79  
% 7.74/2.79  Ordering : KBO
% 7.74/2.79  
% 7.74/2.79  Simplification rules
% 7.74/2.79  ----------------------
% 7.74/2.79  #Subsume      : 155
% 7.74/2.79  #Demod        : 1804
% 7.74/2.79  #Tautology    : 1191
% 7.74/2.79  #SimpNegUnit  : 8
% 7.74/2.79  #BackRed      : 301
% 7.74/2.79  
% 7.74/2.79  #Partial instantiations: 0
% 7.74/2.79  #Strategies tried      : 1
% 7.74/2.79  
% 7.74/2.79  Timing (in seconds)
% 7.74/2.79  ----------------------
% 7.74/2.79  Preprocessing        : 0.37
% 7.74/2.79  Parsing              : 0.20
% 7.74/2.79  CNF conversion       : 0.02
% 7.74/2.79  Main loop            : 1.62
% 7.74/2.79  Inferencing          : 0.58
% 7.74/2.79  Reduction            : 0.53
% 7.74/2.79  Demodulation         : 0.37
% 7.74/2.79  BG Simplification    : 0.07
% 7.74/2.79  Subsumption          : 0.28
% 7.74/2.79  Abstraction          : 0.07
% 7.74/2.79  MUC search           : 0.00
% 7.74/2.79  Cooper               : 0.00
% 7.74/2.79  Total                : 2.06
% 7.74/2.79  Index Insertion      : 0.00
% 7.74/2.79  Index Deletion       : 0.00
% 7.74/2.79  Index Matching       : 0.00
% 7.74/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
