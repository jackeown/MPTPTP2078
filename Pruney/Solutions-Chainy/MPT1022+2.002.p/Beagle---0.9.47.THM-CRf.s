%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:13 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :  242 (1477 expanded)
%              Number of leaves         :   45 ( 514 expanded)
%              Depth                    :   19
%              Number of atoms          :  440 (3920 expanded)
%              Number of equality atoms :  168 (1245 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_66,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4513,plain,(
    ! [A_593,B_594,C_595,D_596] :
      ( k8_relset_1(A_593,B_594,C_595,D_596) = k10_relat_1(C_595,D_596)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4525,plain,(
    ! [D_596] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_596) = k10_relat_1('#skF_3',D_596) ),
    inference(resolution,[status(thm)],[c_68,c_4513])).

tff(c_1317,plain,(
    ! [C_219,A_220,B_221] :
      ( v1_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1326,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1317])).

tff(c_70,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2510,plain,(
    ! [C_375,A_376,B_377] :
      ( v2_funct_1(C_375)
      | ~ v3_funct_2(C_375,A_376,B_377)
      | ~ v1_funct_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2526,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2510])).

tff(c_2534,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2526])).

tff(c_1363,plain,(
    ! [C_225,B_226,A_227] :
      ( v5_relat_1(C_225,B_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1372,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1363])).

tff(c_1625,plain,(
    ! [B_264,A_265] :
      ( k2_relat_1(B_264) = A_265
      | ~ v2_funct_2(B_264,A_265)
      | ~ v5_relat_1(B_264,A_265)
      | ~ v1_relat_1(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1637,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1372,c_1625])).

tff(c_1647,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1637])).

tff(c_1648,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1647])).

tff(c_2131,plain,(
    ! [C_333,B_334,A_335] :
      ( v2_funct_2(C_333,B_334)
      | ~ v3_funct_2(C_333,A_335,B_334)
      | ~ v1_funct_1(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_335,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2144,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2131])).

tff(c_2149,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2144])).

tff(c_2151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1648,c_2149])).

tff(c_2152,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1647])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1334,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1326,c_18])).

tff(c_1336,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1334])).

tff(c_2154,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_1336])).

tff(c_2595,plain,(
    ! [A_386,B_387,C_388,D_389] :
      ( k8_relset_1(A_386,B_387,C_388,D_389) = k10_relat_1(C_388,D_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2610,plain,(
    ! [D_389] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_389) = k10_relat_1('#skF_3',D_389) ),
    inference(resolution,[status(thm)],[c_68,c_2595])).

tff(c_3367,plain,(
    ! [B_469,A_470,C_471] :
      ( k1_xboole_0 = B_469
      | k8_relset_1(A_470,B_469,C_471,B_469) = A_470
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_470,B_469)))
      | ~ v1_funct_2(C_471,A_470,B_469)
      | ~ v1_funct_1(C_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3378,plain,
    ( k1_xboole_0 = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3367])).

tff(c_3387,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2610,c_3378])).

tff(c_3388,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2154,c_3387])).

tff(c_2712,plain,(
    ! [B_401,A_402] :
      ( k9_relat_1(B_401,k10_relat_1(B_401,A_402)) = A_402
      | ~ r1_tarski(A_402,k2_relat_1(B_401))
      | ~ v1_funct_1(B_401)
      | ~ v1_relat_1(B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3051,plain,(
    ! [B_443] :
      ( k9_relat_1(B_443,k10_relat_1(B_443,k2_relat_1(B_443))) = k2_relat_1(B_443)
      | ~ v1_funct_1(B_443)
      | ~ v1_relat_1(B_443) ) ),
    inference(resolution,[status(thm)],[c_6,c_2712])).

tff(c_3068,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_3051])).

tff(c_3076,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_74,c_2152,c_3068])).

tff(c_3389,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3388,c_3076])).

tff(c_3258,plain,(
    ! [B_461,A_462,C_463] :
      ( k1_xboole_0 = B_461
      | k8_relset_1(A_462,B_461,C_463,B_461) = A_462
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_462,B_461)))
      | ~ v1_funct_2(C_463,A_462,B_461)
      | ~ v1_funct_1(C_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3269,plain,
    ( k1_xboole_0 = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3258])).

tff(c_3278,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2610,c_3269])).

tff(c_3279,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2154,c_3278])).

tff(c_3280,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3279,c_3076])).

tff(c_2436,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( k7_relset_1(A_364,B_365,C_366,D_367) = k9_relat_1(C_366,D_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2451,plain,(
    ! [D_367] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_367) = k9_relat_1('#skF_3',D_367) ),
    inference(resolution,[status(thm)],[c_68,c_2436])).

tff(c_2236,plain,(
    ! [A_346,B_347,C_348] :
      ( k1_relset_1(A_346,B_347,C_348) = k1_relat_1(C_348)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2248,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2236])).

tff(c_3093,plain,(
    ! [B_444,A_445,C_446] :
      ( k8_relset_1(B_444,A_445,C_446,k7_relset_1(B_444,A_445,C_446,B_444)) = k1_relset_1(B_444,A_445,C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(B_444,A_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3104,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3093])).

tff(c_3110,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_2451,c_2248,c_3104])).

tff(c_2714,plain,(
    ! [A_402] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_402)) = A_402
      | ~ r1_tarski(A_402,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_2712])).

tff(c_2725,plain,(
    ! [A_402] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_402)) = A_402
      | ~ r1_tarski(A_402,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_74,c_2714])).

tff(c_3114,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k9_relat_1('#skF_3','#skF_1')
    | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3110,c_2725])).

tff(c_3148,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3114])).

tff(c_3290,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3280,c_3148])).

tff(c_3294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3290])).

tff(c_3296,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3114])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3299,plain,
    ( k9_relat_1('#skF_3','#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3296,c_2])).

tff(c_3306,plain,(
    ~ r1_tarski('#skF_1',k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3299])).

tff(c_3399,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3389,c_3306])).

tff(c_3405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3399])).

tff(c_3406,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3299])).

tff(c_3410,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3406,c_3110])).

tff(c_3492,plain,(
    ! [B_477,A_478,C_479] :
      ( k1_xboole_0 = B_477
      | k8_relset_1(A_478,B_477,C_479,B_477) = A_478
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_478,B_477)))
      | ~ v1_funct_2(C_479,A_478,B_477)
      | ~ v1_funct_1(C_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3503,plain,
    ( k1_xboole_0 = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3492])).

tff(c_3512,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3410,c_2610,c_3503])).

tff(c_3513,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2154,c_3512])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k9_relat_1(B_12,A_11)) = A_11
      | ~ v2_funct_1(B_12)
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3549,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_11)) = A_11
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3513,c_24])).

tff(c_3769,plain,(
    ! [A_487] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_487)) = A_487
      | ~ r1_tarski(A_487,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_74,c_2534,c_3549])).

tff(c_91,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_100,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_91])).

tff(c_280,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_289,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_280])).

tff(c_434,plain,(
    ! [B_101,A_102] :
      ( k2_relat_1(B_101) = A_102
      | ~ v2_funct_2(B_101,A_102)
      | ~ v5_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_446,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_289,c_434])).

tff(c_456,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_446])).

tff(c_457,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_781,plain,(
    ! [C_155,B_156,A_157] :
      ( v2_funct_2(C_155,B_156)
      | ~ v3_funct_2(C_155,A_157,B_156)
      | ~ v1_funct_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_794,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_781])).

tff(c_799,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_794])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_799])).

tff(c_802,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_1140,plain,(
    ! [B_195,A_196] :
      ( k9_relat_1(B_195,k10_relat_1(B_195,A_196)) = A_196
      | ~ r1_tarski(A_196,k2_relat_1(B_195))
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1142,plain,(
    ! [A_196] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_196)) = A_196
      | ~ r1_tarski(A_196,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_1140])).

tff(c_1153,plain,(
    ! [A_196] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_196)) = A_196
      | ~ r1_tarski(A_196,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_74,c_1142])).

tff(c_1241,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k8_relset_1(A_207,B_208,C_209,D_210) = k10_relat_1(C_209,D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1256,plain,(
    ! [D_210] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_210) = k10_relat_1('#skF_3',D_210) ),
    inference(resolution,[status(thm)],[c_68,c_1241])).

tff(c_1060,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k7_relset_1(A_179,B_180,C_181,D_182) = k9_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1075,plain,(
    ! [D_182] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_182) = k9_relat_1('#skF_3',D_182) ),
    inference(resolution,[status(thm)],[c_68,c_1060])).

tff(c_64,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_83,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1088,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_83])).

tff(c_1257,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1088])).

tff(c_1269,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1257])).

tff(c_1273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1269])).

tff(c_1274,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2452,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_1274])).

tff(c_2612,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_2452])).

tff(c_3782,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_2612])).

tff(c_3815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3782])).

tff(c_3816,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1334])).

tff(c_20,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1333,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1326,c_20])).

tff(c_1335,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_3818,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_1335])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3822,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_8])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3928,plain,(
    ! [C_508,A_509,B_510] :
      ( v4_relat_1(C_508,A_509)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_509,B_510))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3938,plain,(
    ! [A_511,A_512,B_513] :
      ( v4_relat_1(A_511,A_512)
      | ~ r1_tarski(A_511,k2_zfmisc_1(A_512,B_513)) ) ),
    inference(resolution,[status(thm)],[c_12,c_3928])).

tff(c_3952,plain,(
    ! [A_512] : v4_relat_1('#skF_3',A_512) ),
    inference(resolution,[status(thm)],[c_3822,c_3938])).

tff(c_3874,plain,(
    ! [B_498,A_499] :
      ( r1_tarski(k1_relat_1(B_498),A_499)
      | ~ v4_relat_1(B_498,A_499)
      | ~ v1_relat_1(B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1287,plain,(
    ! [B_216,A_217] :
      ( B_216 = A_217
      | ~ r1_tarski(B_216,A_217)
      | ~ r1_tarski(A_217,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1301,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1287])).

tff(c_3819,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_3816,c_1301])).

tff(c_3968,plain,(
    ! [B_520] :
      ( k1_relat_1(B_520) = '#skF_3'
      | ~ v4_relat_1(B_520,'#skF_3')
      | ~ v1_relat_1(B_520) ) ),
    inference(resolution,[status(thm)],[c_3874,c_3819])).

tff(c_3976,plain,
    ( k1_relat_1('#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3952,c_3968])).

tff(c_3982,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_3976])).

tff(c_3984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3818,c_3982])).

tff(c_3985,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_62,plain,(
    ! [B_43,A_42,C_44] :
      ( k1_xboole_0 = B_43
      | k8_relset_1(A_42,B_43,C_44,B_43) = A_42
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5341,plain,(
    ! [B_687,A_688,C_689] :
      ( B_687 = '#skF_3'
      | k8_relset_1(A_688,B_687,C_689,B_687) = A_688
      | ~ m1_subset_1(C_689,k1_zfmisc_1(k2_zfmisc_1(A_688,B_687)))
      | ~ v1_funct_2(C_689,A_688,B_687)
      | ~ v1_funct_1(C_689) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3985,c_62])).

tff(c_5350,plain,
    ( '#skF_3' = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5341])).

tff(c_5355,plain,
    ( '#skF_3' = '#skF_1'
    | k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4525,c_5350])).

tff(c_5356,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5355])).

tff(c_4765,plain,(
    ! [C_635,B_636,A_637] :
      ( v2_funct_2(C_635,B_636)
      | ~ v3_funct_2(C_635,A_637,B_636)
      | ~ v1_funct_1(C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_637,B_636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4778,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4765])).

tff(c_4783,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_4778])).

tff(c_3990,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3985,c_8])).

tff(c_4054,plain,(
    ! [C_532,B_533,A_534] :
      ( v5_relat_1(C_532,B_533)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_534,B_533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4088,plain,(
    ! [A_542,B_543,A_544] :
      ( v5_relat_1(A_542,B_543)
      | ~ r1_tarski(A_542,k2_zfmisc_1(A_544,B_543)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4054])).

tff(c_4097,plain,(
    ! [B_543] : v5_relat_1('#skF_3',B_543) ),
    inference(resolution,[status(thm)],[c_3990,c_4088])).

tff(c_4287,plain,(
    ! [B_564,A_565] :
      ( k2_relat_1(B_564) = A_565
      | ~ v2_funct_2(B_564,A_565)
      | ~ v5_relat_1(B_564,A_565)
      | ~ v1_relat_1(B_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4293,plain,(
    ! [B_543] :
      ( k2_relat_1('#skF_3') = B_543
      | ~ v2_funct_2('#skF_3',B_543)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4097,c_4287])).

tff(c_4299,plain,(
    ! [B_543] :
      ( k2_relat_1('#skF_3') = B_543
      | ~ v2_funct_2('#skF_3',B_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_4293])).

tff(c_4787,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4783,c_4299])).

tff(c_4385,plain,(
    ! [A_578,B_579,C_580] :
      ( k2_relset_1(A_578,B_579,C_580) = k2_relat_1(C_580)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(A_578,B_579))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4724,plain,(
    ! [A_628,B_629,A_630] :
      ( k2_relset_1(A_628,B_629,A_630) = k2_relat_1(A_630)
      | ~ r1_tarski(A_630,k2_zfmisc_1(A_628,B_629)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4385])).

tff(c_4741,plain,(
    ! [A_628,B_629] : k2_relset_1(A_628,B_629,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3990,c_4724])).

tff(c_4788,plain,(
    ! [A_628,B_629] : k2_relset_1(A_628,B_629,'#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4787,c_4741])).

tff(c_4554,plain,(
    ! [A_602,B_603,C_604,D_605] :
      ( k7_relset_1(A_602,B_603,C_604,D_605) = k9_relat_1(C_604,D_605)
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_602,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4566,plain,(
    ! [D_605] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_605) = k9_relat_1('#skF_3',D_605) ),
    inference(resolution,[status(thm)],[c_68,c_4554])).

tff(c_5088,plain,(
    ! [B_663,A_664,C_665] :
      ( k7_relset_1(B_663,A_664,C_665,k8_relset_1(B_663,A_664,C_665,A_664)) = k2_relset_1(B_663,A_664,C_665)
      | ~ m1_subset_1(C_665,k1_zfmisc_1(k2_zfmisc_1(B_663,A_664))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5097,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) = k2_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5088])).

tff(c_5101,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4788,c_4566,c_4525,c_5097])).

tff(c_5357,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5356,c_5101])).

tff(c_5232,plain,(
    ! [B_684,A_685,C_686] :
      ( B_684 = '#skF_3'
      | k8_relset_1(A_685,B_684,C_686,B_684) = A_685
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(A_685,B_684)))
      | ~ v1_funct_2(C_686,A_685,B_684)
      | ~ v1_funct_1(C_686) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3985,c_62])).

tff(c_5241,plain,
    ( '#skF_3' = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5232])).

tff(c_5246,plain,
    ( '#skF_3' = '#skF_1'
    | k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_4525,c_5241])).

tff(c_5247,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5246])).

tff(c_5248,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5247,c_5101])).

tff(c_3986,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_3995,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3985,c_3986])).

tff(c_4333,plain,(
    ! [A_573,B_574,C_575] :
      ( k1_relset_1(A_573,B_574,C_575) = k1_relat_1(C_575)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4663,plain,(
    ! [A_618,B_619,A_620] :
      ( k1_relset_1(A_618,B_619,A_620) = k1_relat_1(A_620)
      | ~ r1_tarski(A_620,k2_zfmisc_1(A_618,B_619)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4333])).

tff(c_4674,plain,(
    ! [A_618,B_619] : k1_relset_1(A_618,B_619,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3990,c_4663])).

tff(c_4681,plain,(
    ! [A_618,B_619] : k1_relset_1(A_618,B_619,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_4674])).

tff(c_5144,plain,(
    ! [B_671,A_672,C_673] :
      ( k8_relset_1(B_671,A_672,C_673,k7_relset_1(B_671,A_672,C_673,B_671)) = k1_relset_1(B_671,A_672,C_673)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(B_671,A_672))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5153,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) = k1_relset_1('#skF_1','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5144])).

tff(c_5157,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4681,c_4525,c_4566,c_5153])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( k9_relat_1(B_10,k10_relat_1(B_10,A_9)) = A_9
      | ~ r1_tarski(A_9,k2_relat_1(B_10))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4795,plain,(
    ! [A_9] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_9)) = A_9
      | ~ r1_tarski(A_9,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4787,c_22])).

tff(c_4817,plain,(
    ! [A_9] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_9)) = A_9
      | ~ r1_tarski(A_9,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_74,c_4795])).

tff(c_5164,plain,
    ( k9_relat_1('#skF_3','#skF_3') = k9_relat_1('#skF_3','#skF_1')
    | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5157,c_4817])).

tff(c_5230,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5164])).

tff(c_5258,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5248,c_5230])).

tff(c_5262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5258])).

tff(c_5263,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5246])).

tff(c_4692,plain,(
    ! [C_623,A_624,B_625] :
      ( v2_funct_1(C_623)
      | ~ v3_funct_2(C_623,A_624,B_625)
      | ~ v1_funct_1(C_623)
      | ~ m1_subset_1(C_623,k1_zfmisc_1(k2_zfmisc_1(A_624,B_625))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4705,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4692])).

tff(c_4710,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_4705])).

tff(c_4948,plain,(
    ! [B_646,A_647] :
      ( k10_relat_1(B_646,k9_relat_1(B_646,A_647)) = A_647
      | ~ v2_funct_1(B_646)
      | ~ r1_tarski(A_647,k1_relat_1(B_646))
      | ~ v1_funct_1(B_646)
      | ~ v1_relat_1(B_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4956,plain,(
    ! [A_647] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_647)) = A_647
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_647,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3995,c_4948])).

tff(c_4976,plain,(
    ! [A_651] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_651)) = A_651
      | ~ r1_tarski(A_651,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_74,c_4710,c_4956])).

tff(c_4526,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4525,c_1274])).

tff(c_4574,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4566,c_4526])).

tff(c_5001,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4976,c_4574])).

tff(c_5275,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5263,c_5001])).

tff(c_5324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5275])).

tff(c_5326,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5164])).

tff(c_5329,plain,
    ( k9_relat_1('#skF_3','#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5326,c_2])).

tff(c_5339,plain,(
    ~ r1_tarski('#skF_1',k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5329])).

tff(c_5367,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5357,c_5339])).

tff(c_5373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5367])).

tff(c_5374,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5355])).

tff(c_5388,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5374,c_5001])).

tff(c_5437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5388])).

tff(c_5438,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5329])).

tff(c_5442,plain,(
    k10_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5438,c_5157])).

tff(c_5474,plain,(
    ! [B_690,A_691,C_692] :
      ( B_690 = '#skF_3'
      | k8_relset_1(A_691,B_690,C_692,B_690) = A_691
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_691,B_690)))
      | ~ v1_funct_2(C_692,A_691,B_690)
      | ~ v1_funct_1(C_692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3985,c_62])).

tff(c_5483,plain,
    ( '#skF_3' = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_5474])).

tff(c_5488,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_5442,c_4525,c_5483])).

tff(c_5499,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5488,c_5001])).

tff(c_5548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.23  
% 5.84/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.23  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.84/2.23  
% 5.84/2.23  %Foreground sorts:
% 5.84/2.23  
% 5.84/2.23  
% 5.84/2.23  %Background operators:
% 5.84/2.23  
% 5.84/2.23  
% 5.84/2.23  %Foreground operators:
% 5.84/2.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.84/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.84/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.84/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.84/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.84/2.23  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.84/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.84/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.84/2.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.84/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.84/2.23  tff('#skF_1', type, '#skF_1': $i).
% 5.84/2.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.84/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.84/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.84/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.84/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.84/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.84/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.84/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.84/2.23  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.84/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.84/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.84/2.23  
% 6.14/2.26  tff(f_158, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 6.14/2.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.14/2.26  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.14/2.26  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.14/2.26  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.14/2.26  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.14/2.26  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.14/2.26  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 6.14/2.26  tff(f_143, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 6.14/2.26  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 6.14/2.26  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.14/2.26  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.14/2.26  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 6.14/2.26  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 6.14/2.26  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.14/2.26  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.14/2.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.14/2.26  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.14/2.26  tff(c_66, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.14/2.26  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.14/2.26  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.14/2.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.14/2.26  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.14/2.26  tff(c_4513, plain, (![A_593, B_594, C_595, D_596]: (k8_relset_1(A_593, B_594, C_595, D_596)=k10_relat_1(C_595, D_596) | ~m1_subset_1(C_595, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.14/2.26  tff(c_4525, plain, (![D_596]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_596)=k10_relat_1('#skF_3', D_596))), inference(resolution, [status(thm)], [c_68, c_4513])).
% 6.14/2.26  tff(c_1317, plain, (![C_219, A_220, B_221]: (v1_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.14/2.26  tff(c_1326, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1317])).
% 6.14/2.26  tff(c_70, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.14/2.26  tff(c_2510, plain, (![C_375, A_376, B_377]: (v2_funct_1(C_375) | ~v3_funct_2(C_375, A_376, B_377) | ~v1_funct_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.14/2.26  tff(c_2526, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2510])).
% 6.14/2.26  tff(c_2534, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2526])).
% 6.14/2.26  tff(c_1363, plain, (![C_225, B_226, A_227]: (v5_relat_1(C_225, B_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.14/2.26  tff(c_1372, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1363])).
% 6.14/2.26  tff(c_1625, plain, (![B_264, A_265]: (k2_relat_1(B_264)=A_265 | ~v2_funct_2(B_264, A_265) | ~v5_relat_1(B_264, A_265) | ~v1_relat_1(B_264))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.14/2.26  tff(c_1637, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1372, c_1625])).
% 6.14/2.26  tff(c_1647, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1637])).
% 6.14/2.26  tff(c_1648, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1647])).
% 6.14/2.26  tff(c_2131, plain, (![C_333, B_334, A_335]: (v2_funct_2(C_333, B_334) | ~v3_funct_2(C_333, A_335, B_334) | ~v1_funct_1(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_335, B_334))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.14/2.26  tff(c_2144, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2131])).
% 6.14/2.26  tff(c_2149, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2144])).
% 6.14/2.26  tff(c_2151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1648, c_2149])).
% 6.14/2.26  tff(c_2152, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1647])).
% 6.14/2.26  tff(c_18, plain, (![A_8]: (k2_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.14/2.26  tff(c_1334, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1326, c_18])).
% 6.14/2.26  tff(c_1336, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1334])).
% 6.14/2.26  tff(c_2154, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_1336])).
% 6.14/2.26  tff(c_2595, plain, (![A_386, B_387, C_388, D_389]: (k8_relset_1(A_386, B_387, C_388, D_389)=k10_relat_1(C_388, D_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.14/2.26  tff(c_2610, plain, (![D_389]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_389)=k10_relat_1('#skF_3', D_389))), inference(resolution, [status(thm)], [c_68, c_2595])).
% 6.14/2.26  tff(c_3367, plain, (![B_469, A_470, C_471]: (k1_xboole_0=B_469 | k8_relset_1(A_470, B_469, C_471, B_469)=A_470 | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_470, B_469))) | ~v1_funct_2(C_471, A_470, B_469) | ~v1_funct_1(C_471))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.14/2.26  tff(c_3378, plain, (k1_xboole_0='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3367])).
% 6.14/2.26  tff(c_3387, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2610, c_3378])).
% 6.14/2.26  tff(c_3388, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2154, c_3387])).
% 6.14/2.26  tff(c_2712, plain, (![B_401, A_402]: (k9_relat_1(B_401, k10_relat_1(B_401, A_402))=A_402 | ~r1_tarski(A_402, k2_relat_1(B_401)) | ~v1_funct_1(B_401) | ~v1_relat_1(B_401))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.14/2.26  tff(c_3051, plain, (![B_443]: (k9_relat_1(B_443, k10_relat_1(B_443, k2_relat_1(B_443)))=k2_relat_1(B_443) | ~v1_funct_1(B_443) | ~v1_relat_1(B_443))), inference(resolution, [status(thm)], [c_6, c_2712])).
% 6.14/2.26  tff(c_3068, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2152, c_3051])).
% 6.14/2.26  tff(c_3076, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_74, c_2152, c_3068])).
% 6.14/2.26  tff(c_3389, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3388, c_3076])).
% 6.14/2.26  tff(c_3258, plain, (![B_461, A_462, C_463]: (k1_xboole_0=B_461 | k8_relset_1(A_462, B_461, C_463, B_461)=A_462 | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_462, B_461))) | ~v1_funct_2(C_463, A_462, B_461) | ~v1_funct_1(C_463))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.14/2.26  tff(c_3269, plain, (k1_xboole_0='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3258])).
% 6.14/2.26  tff(c_3278, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2610, c_3269])).
% 6.14/2.26  tff(c_3279, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2154, c_3278])).
% 6.14/2.26  tff(c_3280, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3279, c_3076])).
% 6.14/2.26  tff(c_2436, plain, (![A_364, B_365, C_366, D_367]: (k7_relset_1(A_364, B_365, C_366, D_367)=k9_relat_1(C_366, D_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.14/2.26  tff(c_2451, plain, (![D_367]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_367)=k9_relat_1('#skF_3', D_367))), inference(resolution, [status(thm)], [c_68, c_2436])).
% 6.14/2.26  tff(c_2236, plain, (![A_346, B_347, C_348]: (k1_relset_1(A_346, B_347, C_348)=k1_relat_1(C_348) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.14/2.26  tff(c_2248, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2236])).
% 6.14/2.26  tff(c_3093, plain, (![B_444, A_445, C_446]: (k8_relset_1(B_444, A_445, C_446, k7_relset_1(B_444, A_445, C_446, B_444))=k1_relset_1(B_444, A_445, C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(B_444, A_445))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.14/2.26  tff(c_3104, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_3093])).
% 6.14/2.26  tff(c_3110, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_2451, c_2248, c_3104])).
% 6.14/2.26  tff(c_2714, plain, (![A_402]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_402))=A_402 | ~r1_tarski(A_402, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2152, c_2712])).
% 6.14/2.26  tff(c_2725, plain, (![A_402]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_402))=A_402 | ~r1_tarski(A_402, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_74, c_2714])).
% 6.14/2.26  tff(c_3114, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k9_relat_1('#skF_3', '#skF_1') | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3110, c_2725])).
% 6.14/2.26  tff(c_3148, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3114])).
% 6.14/2.27  tff(c_3290, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3280, c_3148])).
% 6.14/2.27  tff(c_3294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3290])).
% 6.14/2.27  tff(c_3296, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_3114])).
% 6.14/2.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.14/2.27  tff(c_3299, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_3296, c_2])).
% 6.14/2.27  tff(c_3306, plain, (~r1_tarski('#skF_1', k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3299])).
% 6.14/2.27  tff(c_3399, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3389, c_3306])).
% 6.14/2.27  tff(c_3405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3399])).
% 6.14/2.27  tff(c_3406, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_3299])).
% 6.14/2.27  tff(c_3410, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3406, c_3110])).
% 6.14/2.27  tff(c_3492, plain, (![B_477, A_478, C_479]: (k1_xboole_0=B_477 | k8_relset_1(A_478, B_477, C_479, B_477)=A_478 | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_478, B_477))) | ~v1_funct_2(C_479, A_478, B_477) | ~v1_funct_1(C_479))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.14/2.27  tff(c_3503, plain, (k1_xboole_0='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3492])).
% 6.14/2.27  tff(c_3512, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3410, c_2610, c_3503])).
% 6.14/2.27  tff(c_3513, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2154, c_3512])).
% 6.14/2.27  tff(c_24, plain, (![B_12, A_11]: (k10_relat_1(B_12, k9_relat_1(B_12, A_11))=A_11 | ~v2_funct_1(B_12) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.14/2.27  tff(c_3549, plain, (![A_11]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_11))=A_11 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_11, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3513, c_24])).
% 6.14/2.27  tff(c_3769, plain, (![A_487]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_487))=A_487 | ~r1_tarski(A_487, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_74, c_2534, c_3549])).
% 6.14/2.27  tff(c_91, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.14/2.27  tff(c_100, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_91])).
% 6.14/2.27  tff(c_280, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.14/2.27  tff(c_289, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_280])).
% 6.14/2.27  tff(c_434, plain, (![B_101, A_102]: (k2_relat_1(B_101)=A_102 | ~v2_funct_2(B_101, A_102) | ~v5_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.14/2.27  tff(c_446, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_289, c_434])).
% 6.14/2.27  tff(c_456, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_446])).
% 6.14/2.27  tff(c_457, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_456])).
% 6.14/2.27  tff(c_781, plain, (![C_155, B_156, A_157]: (v2_funct_2(C_155, B_156) | ~v3_funct_2(C_155, A_157, B_156) | ~v1_funct_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.14/2.27  tff(c_794, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_781])).
% 6.14/2.27  tff(c_799, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_794])).
% 6.14/2.27  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_799])).
% 6.14/2.27  tff(c_802, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_456])).
% 6.14/2.27  tff(c_1140, plain, (![B_195, A_196]: (k9_relat_1(B_195, k10_relat_1(B_195, A_196))=A_196 | ~r1_tarski(A_196, k2_relat_1(B_195)) | ~v1_funct_1(B_195) | ~v1_relat_1(B_195))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.14/2.27  tff(c_1142, plain, (![A_196]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_196))=A_196 | ~r1_tarski(A_196, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_802, c_1140])).
% 6.14/2.27  tff(c_1153, plain, (![A_196]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_196))=A_196 | ~r1_tarski(A_196, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_74, c_1142])).
% 6.14/2.27  tff(c_1241, plain, (![A_207, B_208, C_209, D_210]: (k8_relset_1(A_207, B_208, C_209, D_210)=k10_relat_1(C_209, D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.14/2.27  tff(c_1256, plain, (![D_210]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_210)=k10_relat_1('#skF_3', D_210))), inference(resolution, [status(thm)], [c_68, c_1241])).
% 6.14/2.27  tff(c_1060, plain, (![A_179, B_180, C_181, D_182]: (k7_relset_1(A_179, B_180, C_181, D_182)=k9_relat_1(C_181, D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.14/2.27  tff(c_1075, plain, (![D_182]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_182)=k9_relat_1('#skF_3', D_182))), inference(resolution, [status(thm)], [c_68, c_1060])).
% 6.14/2.27  tff(c_64, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.14/2.27  tff(c_83, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 6.14/2.27  tff(c_1088, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_83])).
% 6.14/2.27  tff(c_1257, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1256, c_1088])).
% 6.14/2.27  tff(c_1269, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1257])).
% 6.14/2.27  tff(c_1273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1269])).
% 6.14/2.27  tff(c_1274, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 6.14/2.27  tff(c_2452, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_1274])).
% 6.14/2.27  tff(c_2612, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_2452])).
% 6.14/2.27  tff(c_3782, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3769, c_2612])).
% 6.14/2.27  tff(c_3815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3782])).
% 6.14/2.27  tff(c_3816, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1334])).
% 6.14/2.27  tff(c_20, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.14/2.27  tff(c_1333, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1326, c_20])).
% 6.14/2.27  tff(c_1335, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1333])).
% 6.14/2.27  tff(c_3818, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_1335])).
% 6.14/2.27  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.14/2.27  tff(c_3822, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_8])).
% 6.14/2.27  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.14/2.27  tff(c_3928, plain, (![C_508, A_509, B_510]: (v4_relat_1(C_508, A_509) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_509, B_510))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.14/2.27  tff(c_3938, plain, (![A_511, A_512, B_513]: (v4_relat_1(A_511, A_512) | ~r1_tarski(A_511, k2_zfmisc_1(A_512, B_513)))), inference(resolution, [status(thm)], [c_12, c_3928])).
% 6.14/2.27  tff(c_3952, plain, (![A_512]: (v4_relat_1('#skF_3', A_512))), inference(resolution, [status(thm)], [c_3822, c_3938])).
% 6.14/2.27  tff(c_3874, plain, (![B_498, A_499]: (r1_tarski(k1_relat_1(B_498), A_499) | ~v4_relat_1(B_498, A_499) | ~v1_relat_1(B_498))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.14/2.27  tff(c_1287, plain, (![B_216, A_217]: (B_216=A_217 | ~r1_tarski(B_216, A_217) | ~r1_tarski(A_217, B_216))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.14/2.27  tff(c_1301, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1287])).
% 6.14/2.27  tff(c_3819, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_3816, c_1301])).
% 6.14/2.27  tff(c_3968, plain, (![B_520]: (k1_relat_1(B_520)='#skF_3' | ~v4_relat_1(B_520, '#skF_3') | ~v1_relat_1(B_520))), inference(resolution, [status(thm)], [c_3874, c_3819])).
% 6.14/2.27  tff(c_3976, plain, (k1_relat_1('#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3952, c_3968])).
% 6.14/2.27  tff(c_3982, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_3976])).
% 6.14/2.27  tff(c_3984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3818, c_3982])).
% 6.14/2.27  tff(c_3985, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1333])).
% 6.14/2.27  tff(c_62, plain, (![B_43, A_42, C_44]: (k1_xboole_0=B_43 | k8_relset_1(A_42, B_43, C_44, B_43)=A_42 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.14/2.27  tff(c_5341, plain, (![B_687, A_688, C_689]: (B_687='#skF_3' | k8_relset_1(A_688, B_687, C_689, B_687)=A_688 | ~m1_subset_1(C_689, k1_zfmisc_1(k2_zfmisc_1(A_688, B_687))) | ~v1_funct_2(C_689, A_688, B_687) | ~v1_funct_1(C_689))), inference(demodulation, [status(thm), theory('equality')], [c_3985, c_62])).
% 6.14/2.27  tff(c_5350, plain, ('#skF_3'='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5341])).
% 6.14/2.27  tff(c_5355, plain, ('#skF_3'='#skF_1' | k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4525, c_5350])).
% 6.14/2.27  tff(c_5356, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_5355])).
% 6.14/2.27  tff(c_4765, plain, (![C_635, B_636, A_637]: (v2_funct_2(C_635, B_636) | ~v3_funct_2(C_635, A_637, B_636) | ~v1_funct_1(C_635) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_637, B_636))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.14/2.27  tff(c_4778, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4765])).
% 6.14/2.27  tff(c_4783, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_4778])).
% 6.14/2.27  tff(c_3990, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3985, c_8])).
% 6.14/2.27  tff(c_4054, plain, (![C_532, B_533, A_534]: (v5_relat_1(C_532, B_533) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_534, B_533))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.14/2.27  tff(c_4088, plain, (![A_542, B_543, A_544]: (v5_relat_1(A_542, B_543) | ~r1_tarski(A_542, k2_zfmisc_1(A_544, B_543)))), inference(resolution, [status(thm)], [c_12, c_4054])).
% 6.14/2.27  tff(c_4097, plain, (![B_543]: (v5_relat_1('#skF_3', B_543))), inference(resolution, [status(thm)], [c_3990, c_4088])).
% 6.14/2.27  tff(c_4287, plain, (![B_564, A_565]: (k2_relat_1(B_564)=A_565 | ~v2_funct_2(B_564, A_565) | ~v5_relat_1(B_564, A_565) | ~v1_relat_1(B_564))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.14/2.27  tff(c_4293, plain, (![B_543]: (k2_relat_1('#skF_3')=B_543 | ~v2_funct_2('#skF_3', B_543) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4097, c_4287])).
% 6.14/2.27  tff(c_4299, plain, (![B_543]: (k2_relat_1('#skF_3')=B_543 | ~v2_funct_2('#skF_3', B_543))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_4293])).
% 6.14/2.27  tff(c_4787, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_4783, c_4299])).
% 6.14/2.27  tff(c_4385, plain, (![A_578, B_579, C_580]: (k2_relset_1(A_578, B_579, C_580)=k2_relat_1(C_580) | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(A_578, B_579))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.14/2.27  tff(c_4724, plain, (![A_628, B_629, A_630]: (k2_relset_1(A_628, B_629, A_630)=k2_relat_1(A_630) | ~r1_tarski(A_630, k2_zfmisc_1(A_628, B_629)))), inference(resolution, [status(thm)], [c_12, c_4385])).
% 6.14/2.27  tff(c_4741, plain, (![A_628, B_629]: (k2_relset_1(A_628, B_629, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3990, c_4724])).
% 6.14/2.27  tff(c_4788, plain, (![A_628, B_629]: (k2_relset_1(A_628, B_629, '#skF_3')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4787, c_4741])).
% 6.14/2.27  tff(c_4554, plain, (![A_602, B_603, C_604, D_605]: (k7_relset_1(A_602, B_603, C_604, D_605)=k9_relat_1(C_604, D_605) | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_602, B_603))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.14/2.27  tff(c_4566, plain, (![D_605]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_605)=k9_relat_1('#skF_3', D_605))), inference(resolution, [status(thm)], [c_68, c_4554])).
% 6.14/2.27  tff(c_5088, plain, (![B_663, A_664, C_665]: (k7_relset_1(B_663, A_664, C_665, k8_relset_1(B_663, A_664, C_665, A_664))=k2_relset_1(B_663, A_664, C_665) | ~m1_subset_1(C_665, k1_zfmisc_1(k2_zfmisc_1(B_663, A_664))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.14/2.27  tff(c_5097, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))=k2_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_5088])).
% 6.14/2.27  tff(c_5101, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4788, c_4566, c_4525, c_5097])).
% 6.14/2.27  tff(c_5357, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5356, c_5101])).
% 6.14/2.27  tff(c_5232, plain, (![B_684, A_685, C_686]: (B_684='#skF_3' | k8_relset_1(A_685, B_684, C_686, B_684)=A_685 | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(A_685, B_684))) | ~v1_funct_2(C_686, A_685, B_684) | ~v1_funct_1(C_686))), inference(demodulation, [status(thm), theory('equality')], [c_3985, c_62])).
% 6.14/2.27  tff(c_5241, plain, ('#skF_3'='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5232])).
% 6.14/2.27  tff(c_5246, plain, ('#skF_3'='#skF_1' | k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_4525, c_5241])).
% 6.14/2.27  tff(c_5247, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_5246])).
% 6.14/2.27  tff(c_5248, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5247, c_5101])).
% 6.14/2.27  tff(c_3986, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1333])).
% 6.14/2.27  tff(c_3995, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3985, c_3986])).
% 6.14/2.27  tff(c_4333, plain, (![A_573, B_574, C_575]: (k1_relset_1(A_573, B_574, C_575)=k1_relat_1(C_575) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.14/2.27  tff(c_4663, plain, (![A_618, B_619, A_620]: (k1_relset_1(A_618, B_619, A_620)=k1_relat_1(A_620) | ~r1_tarski(A_620, k2_zfmisc_1(A_618, B_619)))), inference(resolution, [status(thm)], [c_12, c_4333])).
% 6.14/2.27  tff(c_4674, plain, (![A_618, B_619]: (k1_relset_1(A_618, B_619, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3990, c_4663])).
% 6.14/2.27  tff(c_4681, plain, (![A_618, B_619]: (k1_relset_1(A_618, B_619, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3995, c_4674])).
% 6.14/2.27  tff(c_5144, plain, (![B_671, A_672, C_673]: (k8_relset_1(B_671, A_672, C_673, k7_relset_1(B_671, A_672, C_673, B_671))=k1_relset_1(B_671, A_672, C_673) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(B_671, A_672))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.14/2.27  tff(c_5153, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))=k1_relset_1('#skF_1', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_5144])).
% 6.14/2.27  tff(c_5157, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4681, c_4525, c_4566, c_5153])).
% 6.14/2.27  tff(c_22, plain, (![B_10, A_9]: (k9_relat_1(B_10, k10_relat_1(B_10, A_9))=A_9 | ~r1_tarski(A_9, k2_relat_1(B_10)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.14/2.27  tff(c_4795, plain, (![A_9]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_9))=A_9 | ~r1_tarski(A_9, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4787, c_22])).
% 6.14/2.27  tff(c_4817, plain, (![A_9]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_9))=A_9 | ~r1_tarski(A_9, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_74, c_4795])).
% 6.14/2.27  tff(c_5164, plain, (k9_relat_1('#skF_3', '#skF_3')=k9_relat_1('#skF_3', '#skF_1') | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5157, c_4817])).
% 6.14/2.27  tff(c_5230, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5164])).
% 6.14/2.27  tff(c_5258, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5248, c_5230])).
% 6.14/2.27  tff(c_5262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5258])).
% 6.14/2.27  tff(c_5263, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_5246])).
% 6.14/2.27  tff(c_4692, plain, (![C_623, A_624, B_625]: (v2_funct_1(C_623) | ~v3_funct_2(C_623, A_624, B_625) | ~v1_funct_1(C_623) | ~m1_subset_1(C_623, k1_zfmisc_1(k2_zfmisc_1(A_624, B_625))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.14/2.27  tff(c_4705, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4692])).
% 6.14/2.27  tff(c_4710, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_4705])).
% 6.14/2.27  tff(c_4948, plain, (![B_646, A_647]: (k10_relat_1(B_646, k9_relat_1(B_646, A_647))=A_647 | ~v2_funct_1(B_646) | ~r1_tarski(A_647, k1_relat_1(B_646)) | ~v1_funct_1(B_646) | ~v1_relat_1(B_646))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.14/2.27  tff(c_4956, plain, (![A_647]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_647))=A_647 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_647, '#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3995, c_4948])).
% 6.14/2.27  tff(c_4976, plain, (![A_651]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_651))=A_651 | ~r1_tarski(A_651, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_74, c_4710, c_4956])).
% 6.14/2.27  tff(c_4526, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4525, c_1274])).
% 6.14/2.27  tff(c_4574, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4566, c_4526])).
% 6.14/2.27  tff(c_5001, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4976, c_4574])).
% 6.14/2.27  tff(c_5275, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5263, c_5001])).
% 6.14/2.27  tff(c_5324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_5275])).
% 6.14/2.27  tff(c_5326, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_5164])).
% 6.14/2.27  tff(c_5329, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_5326, c_2])).
% 6.14/2.27  tff(c_5339, plain, (~r1_tarski('#skF_1', k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5329])).
% 6.14/2.27  tff(c_5367, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5357, c_5339])).
% 6.14/2.27  tff(c_5373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5367])).
% 6.14/2.27  tff(c_5374, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_5355])).
% 6.14/2.27  tff(c_5388, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5374, c_5001])).
% 6.14/2.27  tff(c_5437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_5388])).
% 6.14/2.27  tff(c_5438, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_5329])).
% 6.14/2.27  tff(c_5442, plain, (k10_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5438, c_5157])).
% 6.14/2.27  tff(c_5474, plain, (![B_690, A_691, C_692]: (B_690='#skF_3' | k8_relset_1(A_691, B_690, C_692, B_690)=A_691 | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_691, B_690))) | ~v1_funct_2(C_692, A_691, B_690) | ~v1_funct_1(C_692))), inference(demodulation, [status(thm), theory('equality')], [c_3985, c_62])).
% 6.14/2.27  tff(c_5483, plain, ('#skF_3'='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_5474])).
% 6.14/2.27  tff(c_5488, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_5442, c_4525, c_5483])).
% 6.14/2.27  tff(c_5499, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5488, c_5001])).
% 6.14/2.27  tff(c_5548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_5499])).
% 6.14/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.14/2.27  
% 6.14/2.27  Inference rules
% 6.14/2.27  ----------------------
% 6.14/2.27  #Ref     : 0
% 6.14/2.27  #Sup     : 1124
% 6.14/2.27  #Fact    : 0
% 6.14/2.27  #Define  : 0
% 6.14/2.27  #Split   : 24
% 6.14/2.27  #Chain   : 0
% 6.14/2.27  #Close   : 0
% 6.14/2.27  
% 6.14/2.27  Ordering : KBO
% 6.14/2.27  
% 6.14/2.27  Simplification rules
% 6.14/2.27  ----------------------
% 6.14/2.27  #Subsume      : 113
% 6.14/2.27  #Demod        : 1221
% 6.14/2.27  #Tautology    : 543
% 6.14/2.27  #SimpNegUnit  : 12
% 6.14/2.27  #BackRed      : 246
% 6.14/2.27  
% 6.14/2.27  #Partial instantiations: 0
% 6.14/2.27  #Strategies tried      : 1
% 6.14/2.27  
% 6.14/2.27  Timing (in seconds)
% 6.14/2.27  ----------------------
% 6.14/2.27  Preprocessing        : 0.38
% 6.14/2.27  Parsing              : 0.22
% 6.14/2.27  CNF conversion       : 0.02
% 6.14/2.27  Main loop            : 1.02
% 6.14/2.27  Inferencing          : 0.37
% 6.14/2.27  Reduction            : 0.34
% 6.14/2.27  Demodulation         : 0.24
% 6.14/2.27  BG Simplification    : 0.04
% 6.14/2.27  Subsumption          : 0.17
% 6.14/2.27  Abstraction          : 0.05
% 6.14/2.27  MUC search           : 0.00
% 6.14/2.27  Cooper               : 0.00
% 6.14/2.27  Total                : 1.47
% 6.14/2.27  Index Insertion      : 0.00
% 6.14/2.27  Index Deletion       : 0.00
% 6.14/2.27  Index Matching       : 0.00
% 6.14/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
