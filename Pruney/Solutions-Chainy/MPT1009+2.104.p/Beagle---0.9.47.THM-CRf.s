%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:56 EST 2020

% Result     : Theorem 9.30s
% Output     : CNFRefutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :  218 (2857 expanded)
%              Number of leaves         :   44 (1003 expanded)
%              Depth                    :   21
%              Number of atoms          :  375 (6386 expanded)
%              Number of equality atoms :   75 (1471 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_169,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_40,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_90,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_161,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_164,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_161])).

tff(c_170,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_164])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,A_24),k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    ! [A_52,B_53] : v1_relat_1(k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_112,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_110])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_257,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_319,plain,(
    ! [A_104,A_105,B_106] :
      ( v4_relat_1(A_104,A_105)
      | ~ r1_tarski(A_104,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(resolution,[status(thm)],[c_28,c_257])).

tff(c_368,plain,(
    ! [A_109,B_110] : v4_relat_1(k2_zfmisc_1(A_109,B_110),A_109) ),
    inference(resolution,[status(thm)],[c_6,c_319])).

tff(c_374,plain,(
    ! [A_11] : v4_relat_1(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_368])).

tff(c_24,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_280,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_388,plain,(
    ! [A_114,B_115,A_116] :
      ( v5_relat_1(A_114,B_115)
      | ~ r1_tarski(A_114,k2_zfmisc_1(A_116,B_115)) ) ),
    inference(resolution,[status(thm)],[c_28,c_280])).

tff(c_415,plain,(
    ! [A_117,B_118] : v5_relat_1(k2_zfmisc_1(A_117,B_118),B_118) ),
    inference(resolution,[status(thm)],[c_6,c_388])).

tff(c_418,plain,(
    ! [B_12] : v5_relat_1(k1_xboole_0,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_415])).

tff(c_18,plain,(
    ! [B_10] : r1_tarski(k1_xboole_0,k1_tarski(B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_346,plain,(
    ! [B_107,A_108] :
      ( k1_tarski(B_107) = A_108
      | k1_xboole_0 = A_108
      | ~ r1_tarski(A_108,k1_tarski(B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11695,plain,(
    ! [B_638,B_639] :
      ( k2_relat_1(B_638) = k1_tarski(B_639)
      | k2_relat_1(B_638) = k1_xboole_0
      | ~ v5_relat_1(B_638,k1_tarski(B_639))
      | ~ v1_relat_1(B_638) ) ),
    inference(resolution,[status(thm)],[c_38,c_346])).

tff(c_11790,plain,(
    ! [B_639] :
      ( k2_relat_1(k1_xboole_0) = k1_tarski(B_639)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_418,c_11695])).

tff(c_11847,plain,(
    ! [B_639] :
      ( k2_relat_1(k1_xboole_0) = k1_tarski(B_639)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_11790])).

tff(c_11852,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_11847])).

tff(c_94,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_8605,plain,(
    ! [B_549,B_550] :
      ( k2_relat_1(B_549) = k1_tarski(B_550)
      | k2_relat_1(B_549) = k1_xboole_0
      | ~ v5_relat_1(B_549,k1_tarski(B_550))
      | ~ v1_relat_1(B_549) ) ),
    inference(resolution,[status(thm)],[c_38,c_346])).

tff(c_8700,plain,(
    ! [B_550] :
      ( k2_relat_1(k1_xboole_0) = k1_tarski(B_550)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_418,c_8605])).

tff(c_8759,plain,(
    ! [B_550] :
      ( k2_relat_1(k1_xboole_0) = k1_tarski(B_550)
      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_8700])).

tff(c_8764,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8759])).

tff(c_239,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k2_relat_1(B_80),A_81)
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_171,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(A_13)
      | ~ v1_relat_1(B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_28,c_161])).

tff(c_491,plain,(
    ! [B_128,A_129] :
      ( v1_relat_1(k2_relat_1(B_128))
      | ~ v1_relat_1(A_129)
      | ~ v5_relat_1(B_128,A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_239,c_171])).

tff(c_493,plain,(
    ! [B_12] :
      ( v1_relat_1(k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_418,c_491])).

tff(c_504,plain,(
    ! [B_12] :
      ( v1_relat_1(k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_493])).

tff(c_525,plain,(
    ! [B_12] : ~ v1_relat_1(B_12) ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_525,c_170])).

tff(c_534,plain,(
    v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_414,plain,(
    ! [A_116,B_115] : v5_relat_1(k2_zfmisc_1(A_116,B_115),B_115) ),
    inference(resolution,[status(thm)],[c_6,c_388])).

tff(c_6447,plain,(
    ! [B_395,B_396,A_397] :
      ( v5_relat_1(k2_relat_1(B_395),B_396)
      | ~ v5_relat_1(B_395,k2_zfmisc_1(A_397,B_396))
      | ~ v1_relat_1(B_395) ) ),
    inference(resolution,[status(thm)],[c_38,c_388])).

tff(c_6453,plain,(
    ! [A_116,A_397,B_396] :
      ( v5_relat_1(k2_relat_1(k2_zfmisc_1(A_116,k2_zfmisc_1(A_397,B_396))),B_396)
      | ~ v1_relat_1(k2_zfmisc_1(A_116,k2_zfmisc_1(A_397,B_396))) ) ),
    inference(resolution,[status(thm)],[c_414,c_6447])).

tff(c_6466,plain,(
    ! [A_116,A_397,B_396] : v5_relat_1(k2_relat_1(k2_zfmisc_1(A_116,k2_zfmisc_1(A_397,B_396))),B_396) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6453])).

tff(c_6581,plain,(
    ! [B_412,A_413] :
      ( m1_subset_1(B_412,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_412),A_413)))
      | ~ r1_tarski(k2_relat_1(B_412),A_413)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7692,plain,(
    ! [B_511] :
      ( m1_subset_1(B_511,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_511),k1_xboole_0)
      | ~ v1_funct_1(B_511)
      | ~ v1_relat_1(B_511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6581])).

tff(c_7698,plain,(
    ! [B_512] :
      ( m1_subset_1(B_512,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(B_512)
      | ~ v5_relat_1(B_512,k1_xboole_0)
      | ~ v1_relat_1(B_512) ) ),
    inference(resolution,[status(thm)],[c_38,c_7692])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8001,plain,(
    ! [B_517] :
      ( r1_tarski(B_517,k1_xboole_0)
      | ~ v1_funct_1(B_517)
      | ~ v5_relat_1(B_517,k1_xboole_0)
      | ~ v1_relat_1(B_517) ) ),
    inference(resolution,[status(thm)],[c_7698,c_26])).

tff(c_8081,plain,(
    ! [A_116,A_397] :
      ( r1_tarski(k2_relat_1(k2_zfmisc_1(A_116,k2_zfmisc_1(A_397,k1_xboole_0))),k1_xboole_0)
      | ~ v1_funct_1(k2_relat_1(k2_zfmisc_1(A_116,k2_zfmisc_1(A_397,k1_xboole_0))))
      | ~ v1_relat_1(k2_relat_1(k2_zfmisc_1(A_116,k2_zfmisc_1(A_397,k1_xboole_0)))) ) ),
    inference(resolution,[status(thm)],[c_6466,c_8001])).

tff(c_8145,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_22,c_22,c_22,c_22,c_22,c_22,c_8081])).

tff(c_8160,plain,(
    ~ v1_funct_1(k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8145])).

tff(c_377,plain,(
    ! [B_112,A_113] :
      ( v1_funct_1(B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_424,plain,(
    ! [A_120,B_121] :
      ( v1_funct_1(A_120)
      | ~ v1_funct_1(B_121)
      | ~ v1_relat_1(B_121)
      | ~ r1_tarski(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_28,c_377])).

tff(c_8232,plain,(
    ! [B_530,A_531] :
      ( v1_funct_1(k2_relat_1(B_530))
      | ~ v1_funct_1(A_531)
      | ~ v1_relat_1(A_531)
      | ~ v5_relat_1(B_530,A_531)
      | ~ v1_relat_1(B_530) ) ),
    inference(resolution,[status(thm)],[c_38,c_424])).

tff(c_8278,plain,(
    ! [B_12] :
      ( v1_funct_1(k2_relat_1(k1_xboole_0))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_418,c_8232])).

tff(c_8337,plain,(
    ! [B_12] :
      ( v1_funct_1(k2_relat_1(k1_xboole_0))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_8278])).

tff(c_8347,plain,(
    ! [B_532] :
      ( ~ v1_funct_1(B_532)
      | ~ v1_relat_1(B_532) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8160,c_8337])).

tff(c_8407,plain,(
    ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_170,c_8347])).

tff(c_8436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8407])).

tff(c_8437,plain,(
    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8145])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8465,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_8437,c_2])).

tff(c_8488,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8465])).

tff(c_8770,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8764,c_8488])).

tff(c_8800,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8770])).

tff(c_8922,plain,(
    ! [B_553] : k2_relat_1(k1_xboole_0) = k1_tarski(B_553) ),
    inference(splitRight,[status(thm)],[c_8759])).

tff(c_8938,plain,(
    ! [B_553] : ~ r1_tarski(k1_xboole_0,k1_tarski(B_553)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8922,c_8488])).

tff(c_9016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8938])).

tff(c_9017,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8465])).

tff(c_9096,plain,(
    ! [A_20] :
      ( r1_tarski(k1_xboole_0,A_20)
      | ~ v5_relat_1(k1_xboole_0,A_20)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9017,c_38])).

tff(c_9121,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_418,c_9096])).

tff(c_535,plain,(
    ! [B_132,A_133] :
      ( k1_tarski(k1_funct_1(B_132,A_133)) = k2_relat_1(B_132)
      | k1_tarski(A_133) != k1_relat_1(B_132)
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_86,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_550,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski('#skF_2') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_86])).

tff(c_558,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski('#skF_2') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_94,c_550])).

tff(c_6375,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_271,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_90,c_257])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9280,plain,(
    ! [B_565,B_566] :
      ( k1_tarski(B_565) = k1_relat_1(B_566)
      | k1_relat_1(B_566) = k1_xboole_0
      | ~ v4_relat_1(B_566,k1_tarski(B_565))
      | ~ v1_relat_1(B_566) ) ),
    inference(resolution,[status(thm)],[c_34,c_346])).

tff(c_9354,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_271,c_9280])).

tff(c_9390,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_9354])).

tff(c_9391,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6375,c_9390])).

tff(c_68,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44),A_43)))
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_9431,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_43)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_43)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9391,c_68])).

tff(c_9472,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_94,c_24,c_9431])).

tff(c_9755,plain,(
    ! [A_571] : ~ r1_tarski(k2_relat_1('#skF_5'),A_571) ),
    inference(splitLeft,[status(thm)],[c_9472])).

tff(c_9767,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_9755])).

tff(c_9768,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_9472])).

tff(c_9816,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9768,c_26])).

tff(c_9872,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_9816,c_2])).

tff(c_9883,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9121,c_9872])).

tff(c_9909,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9883,c_9391])).

tff(c_226,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_570,plain,(
    ! [B_136,A_137] :
      ( v1_relat_1(k1_relat_1(B_136))
      | ~ v1_relat_1(A_137)
      | ~ v4_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_226,c_171])).

tff(c_572,plain,(
    ! [A_11] :
      ( v1_relat_1(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_11)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_374,c_570])).

tff(c_583,plain,(
    ! [A_11] :
      ( v1_relat_1(k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_572])).

tff(c_592,plain,(
    ! [A_11] : ~ v1_relat_1(A_11) ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_534])).

tff(c_604,plain,(
    v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_345,plain,(
    ! [A_105,B_106] : v4_relat_1(k2_zfmisc_1(A_105,B_106),A_105) ),
    inference(resolution,[status(thm)],[c_6,c_319])).

tff(c_6644,plain,(
    ! [B_421,B_422,A_423] :
      ( v5_relat_1(k1_relat_1(B_421),B_422)
      | ~ v4_relat_1(B_421,k2_zfmisc_1(A_423,B_422))
      | ~ v1_relat_1(B_421) ) ),
    inference(resolution,[status(thm)],[c_34,c_388])).

tff(c_6650,plain,(
    ! [A_423,B_422,B_106] :
      ( v5_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423,B_422),B_106)),B_422)
      | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423,B_422),B_106)) ) ),
    inference(resolution,[status(thm)],[c_345,c_6644])).

tff(c_6663,plain,(
    ! [A_423,B_422,B_106] : v5_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423,B_422),B_106)),B_422) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6650])).

tff(c_8057,plain,(
    ! [A_423,B_106] :
      ( r1_tarski(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423,k1_xboole_0),B_106)),k1_xboole_0)
      | ~ v1_funct_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423,k1_xboole_0),B_106)))
      | ~ v1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423,k1_xboole_0),B_106))) ) ),
    inference(resolution,[status(thm)],[c_6663,c_8001])).

tff(c_8133,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_24,c_22,c_24,c_22,c_24,c_22,c_8057])).

tff(c_8159,plain,(
    ~ v1_funct_1(k1_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8133])).

tff(c_9918,plain,(
    ~ v1_funct_1(k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9883,c_8159])).

tff(c_10144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9909,c_9918])).

tff(c_10146,plain,(
    v1_funct_1(k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_8133])).

tff(c_10171,plain,(
    ~ v1_funct_1(k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_8145])).

tff(c_10843,plain,(
    ! [B_603,A_604] :
      ( v1_funct_1(k2_relat_1(B_603))
      | ~ v1_funct_1(A_604)
      | ~ v1_relat_1(A_604)
      | ~ v5_relat_1(B_603,A_604)
      | ~ v1_relat_1(B_603) ) ),
    inference(resolution,[status(thm)],[c_38,c_424])).

tff(c_10889,plain,(
    ! [B_12] :
      ( v1_funct_1(k2_relat_1(k1_xboole_0))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_418,c_10843])).

tff(c_10954,plain,(
    ! [B_12] :
      ( v1_funct_1(k2_relat_1(k1_xboole_0))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_10889])).

tff(c_10964,plain,(
    ! [B_605] :
      ( ~ v1_funct_1(B_605)
      | ~ v1_relat_1(B_605) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10171,c_10954])).

tff(c_11021,plain,(
    ~ v1_funct_1(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_604,c_10964])).

tff(c_11061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10146,c_11021])).

tff(c_11062,plain,(
    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8145])).

tff(c_11090,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_11062,c_2])).

tff(c_11116,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_11090])).

tff(c_11858,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11852,c_11116])).

tff(c_11888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11858])).

tff(c_12007,plain,(
    ! [B_642] : k2_relat_1(k1_xboole_0) = k1_tarski(B_642) ),
    inference(splitRight,[status(thm)],[c_11847])).

tff(c_12023,plain,(
    ! [B_642] : ~ r1_tarski(k1_xboole_0,k1_tarski(B_642)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12007,c_11116])).

tff(c_12101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12023])).

tff(c_12102,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11090])).

tff(c_12181,plain,(
    ! [A_20] :
      ( r1_tarski(k1_xboole_0,A_20)
      | ~ v5_relat_1(k1_xboole_0,A_20)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12102,c_38])).

tff(c_12206,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_418,c_12181])).

tff(c_10145,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8133])).

tff(c_10167,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_10145,c_2])).

tff(c_11115,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_10167])).

tff(c_12214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12206,c_11115])).

tff(c_12215,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10167])).

tff(c_12312,plain,(
    ! [A_18] :
      ( r1_tarski(k1_xboole_0,A_18)
      | ~ v4_relat_1(k1_xboole_0,A_18)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12215,c_34])).

tff(c_12349,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_374,c_12312])).

tff(c_12879,plain,(
    ! [B_668,B_669] :
      ( k1_tarski(B_668) = k1_relat_1(B_669)
      | k1_relat_1(B_669) = k1_xboole_0
      | ~ v4_relat_1(B_669,k1_tarski(B_668))
      | ~ v1_relat_1(B_669) ) ),
    inference(resolution,[status(thm)],[c_34,c_346])).

tff(c_12921,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_271,c_12879])).

tff(c_12937,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_12921])).

tff(c_12938,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_6375,c_12937])).

tff(c_12978,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_43)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_43)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12938,c_68])).

tff(c_13019,plain,(
    ! [A_43] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_94,c_24,c_12978])).

tff(c_13102,plain,(
    ! [A_673] : ~ r1_tarski(k2_relat_1('#skF_5'),A_673) ),
    inference(splitLeft,[status(thm)],[c_13019])).

tff(c_13114,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_13102])).

tff(c_13115,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_13019])).

tff(c_13163,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13115,c_26])).

tff(c_13236,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_13163,c_2])).

tff(c_13254,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12349,c_13236])).

tff(c_13276,plain,(
    ! [A_18] : r1_tarski('#skF_5',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13254,c_12349])).

tff(c_290,plain,(
    ! [C_90,B_12] :
      ( v5_relat_1(C_90,B_12)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_280])).

tff(c_13167,plain,(
    ! [B_676] : v5_relat_1('#skF_5',B_676) ),
    inference(resolution,[status(thm)],[c_13115,c_290])).

tff(c_12366,plain,(
    ! [A_646] : r1_tarski(k1_xboole_0,A_646) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_374,c_12312])).

tff(c_245,plain,(
    ! [B_80,A_81] :
      ( k2_relat_1(B_80) = A_81
      | ~ r1_tarski(A_81,k2_relat_1(B_80))
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_12401,plain,(
    ! [B_80] :
      ( k2_relat_1(B_80) = k1_xboole_0
      | ~ v5_relat_1(B_80,k1_xboole_0)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_12366,c_245])).

tff(c_13175,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_13167,c_12401])).

tff(c_13200,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_13175])).

tff(c_13486,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13254,c_13200])).

tff(c_192,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_202,plain,(
    ! [B_25,A_24] :
      ( k9_relat_1(B_25,A_24) = k2_relat_1(B_25)
      | ~ r1_tarski(k2_relat_1(B_25),k9_relat_1(B_25,A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_42,c_192])).

tff(c_13490,plain,(
    ! [A_24] :
      ( k9_relat_1('#skF_5',A_24) = k2_relat_1('#skF_5')
      | ~ r1_tarski('#skF_5',k9_relat_1('#skF_5',A_24))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13486,c_202])).

tff(c_13509,plain,(
    ! [A_24] : k9_relat_1('#skF_5',A_24) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_13276,c_13486,c_13490])).

tff(c_6515,plain,(
    ! [A_402,B_403,C_404,D_405] :
      ( k7_relset_1(A_402,B_403,C_404,D_405) = k9_relat_1(C_404,D_405)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6525,plain,(
    ! [D_405] : k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5',D_405) = k9_relat_1('#skF_5',D_405) ),
    inference(resolution,[status(thm)],[c_90,c_6515])).

tff(c_6547,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6525,c_86])).

tff(c_13747,plain,(
    ~ r1_tarski('#skF_5',k1_tarski(k1_funct_1('#skF_5','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13509,c_6547])).

tff(c_13751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13276,c_13747])).

tff(c_13753,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_13772,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13753,c_90])).

tff(c_54,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( k7_relset_1(A_36,B_37,C_38,D_39) = k9_relat_1(C_38,D_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_13865,plain,(
    ! [D_39] : k7_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5',D_39) = k9_relat_1('#skF_5',D_39) ),
    inference(resolution,[status(thm)],[c_13772,c_54])).

tff(c_13752,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_13936,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_5'),'#skF_3','#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13753,c_13752])).

tff(c_13950,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13865,c_13936])).

tff(c_13963,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_13950])).

tff(c_13967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_13963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.30/3.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.36  
% 9.30/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.30/3.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.30/3.36  
% 9.30/3.36  %Foreground sorts:
% 9.30/3.36  
% 9.30/3.36  
% 9.30/3.36  %Background operators:
% 9.30/3.36  
% 9.30/3.36  
% 9.30/3.36  %Foreground operators:
% 9.30/3.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.30/3.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.30/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.30/3.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.30/3.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.30/3.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.30/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.30/3.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.30/3.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.30/3.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.30/3.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.30/3.36  tff('#skF_5', type, '#skF_5': $i).
% 9.30/3.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.30/3.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.30/3.36  tff('#skF_2', type, '#skF_2': $i).
% 9.30/3.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.30/3.36  tff('#skF_3', type, '#skF_3': $i).
% 9.30/3.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.30/3.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.30/3.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.30/3.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.30/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.30/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.30/3.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.30/3.36  tff('#skF_4', type, '#skF_4': $i).
% 9.30/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.30/3.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.30/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.30/3.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.30/3.36  
% 9.61/3.39  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.61/3.39  tff(f_169, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 9.61/3.39  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.61/3.39  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 9.61/3.39  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.61/3.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.61/3.39  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.61/3.39  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.61/3.39  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 9.61/3.39  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.61/3.39  tff(f_140, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 9.61/3.39  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 9.61/3.39  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 9.61/3.39  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.61/3.39  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.61/3.39  tff(c_40, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.61/3.39  tff(c_90, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.61/3.39  tff(c_161, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.61/3.39  tff(c_164, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_161])).
% 9.61/3.39  tff(c_170, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_164])).
% 9.61/3.39  tff(c_42, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, A_24), k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.61/3.39  tff(c_22, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.61/3.39  tff(c_110, plain, (![A_52, B_53]: (v1_relat_1(k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.61/3.39  tff(c_112, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_110])).
% 9.61/3.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.39  tff(c_28, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.61/3.39  tff(c_257, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.61/3.39  tff(c_319, plain, (![A_104, A_105, B_106]: (v4_relat_1(A_104, A_105) | ~r1_tarski(A_104, k2_zfmisc_1(A_105, B_106)))), inference(resolution, [status(thm)], [c_28, c_257])).
% 9.61/3.39  tff(c_368, plain, (![A_109, B_110]: (v4_relat_1(k2_zfmisc_1(A_109, B_110), A_109))), inference(resolution, [status(thm)], [c_6, c_319])).
% 9.61/3.39  tff(c_374, plain, (![A_11]: (v4_relat_1(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_22, c_368])).
% 9.61/3.39  tff(c_24, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.61/3.39  tff(c_280, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.61/3.39  tff(c_388, plain, (![A_114, B_115, A_116]: (v5_relat_1(A_114, B_115) | ~r1_tarski(A_114, k2_zfmisc_1(A_116, B_115)))), inference(resolution, [status(thm)], [c_28, c_280])).
% 9.61/3.39  tff(c_415, plain, (![A_117, B_118]: (v5_relat_1(k2_zfmisc_1(A_117, B_118), B_118))), inference(resolution, [status(thm)], [c_6, c_388])).
% 9.61/3.39  tff(c_418, plain, (![B_12]: (v5_relat_1(k1_xboole_0, B_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_415])).
% 9.61/3.39  tff(c_18, plain, (![B_10]: (r1_tarski(k1_xboole_0, k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.61/3.39  tff(c_38, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.61/3.39  tff(c_346, plain, (![B_107, A_108]: (k1_tarski(B_107)=A_108 | k1_xboole_0=A_108 | ~r1_tarski(A_108, k1_tarski(B_107)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.61/3.39  tff(c_11695, plain, (![B_638, B_639]: (k2_relat_1(B_638)=k1_tarski(B_639) | k2_relat_1(B_638)=k1_xboole_0 | ~v5_relat_1(B_638, k1_tarski(B_639)) | ~v1_relat_1(B_638))), inference(resolution, [status(thm)], [c_38, c_346])).
% 9.61/3.39  tff(c_11790, plain, (![B_639]: (k2_relat_1(k1_xboole_0)=k1_tarski(B_639) | k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_418, c_11695])).
% 9.61/3.39  tff(c_11847, plain, (![B_639]: (k2_relat_1(k1_xboole_0)=k1_tarski(B_639) | k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_11790])).
% 9.61/3.39  tff(c_11852, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_11847])).
% 9.61/3.39  tff(c_94, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.61/3.39  tff(c_8605, plain, (![B_549, B_550]: (k2_relat_1(B_549)=k1_tarski(B_550) | k2_relat_1(B_549)=k1_xboole_0 | ~v5_relat_1(B_549, k1_tarski(B_550)) | ~v1_relat_1(B_549))), inference(resolution, [status(thm)], [c_38, c_346])).
% 9.61/3.39  tff(c_8700, plain, (![B_550]: (k2_relat_1(k1_xboole_0)=k1_tarski(B_550) | k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_418, c_8605])).
% 9.61/3.39  tff(c_8759, plain, (![B_550]: (k2_relat_1(k1_xboole_0)=k1_tarski(B_550) | k2_relat_1(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_8700])).
% 9.61/3.39  tff(c_8764, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8759])).
% 9.61/3.39  tff(c_239, plain, (![B_80, A_81]: (r1_tarski(k2_relat_1(B_80), A_81) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.61/3.39  tff(c_171, plain, (![A_13, B_14]: (v1_relat_1(A_13) | ~v1_relat_1(B_14) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_28, c_161])).
% 9.61/3.39  tff(c_491, plain, (![B_128, A_129]: (v1_relat_1(k2_relat_1(B_128)) | ~v1_relat_1(A_129) | ~v5_relat_1(B_128, A_129) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_239, c_171])).
% 9.61/3.39  tff(c_493, plain, (![B_12]: (v1_relat_1(k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_12) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_418, c_491])).
% 9.61/3.39  tff(c_504, plain, (![B_12]: (v1_relat_1(k2_relat_1(k1_xboole_0)) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_493])).
% 9.61/3.39  tff(c_525, plain, (![B_12]: (~v1_relat_1(B_12))), inference(splitLeft, [status(thm)], [c_504])).
% 9.61/3.39  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_525, c_170])).
% 9.61/3.39  tff(c_534, plain, (v1_relat_1(k2_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_504])).
% 9.61/3.39  tff(c_414, plain, (![A_116, B_115]: (v5_relat_1(k2_zfmisc_1(A_116, B_115), B_115))), inference(resolution, [status(thm)], [c_6, c_388])).
% 9.61/3.39  tff(c_6447, plain, (![B_395, B_396, A_397]: (v5_relat_1(k2_relat_1(B_395), B_396) | ~v5_relat_1(B_395, k2_zfmisc_1(A_397, B_396)) | ~v1_relat_1(B_395))), inference(resolution, [status(thm)], [c_38, c_388])).
% 9.61/3.39  tff(c_6453, plain, (![A_116, A_397, B_396]: (v5_relat_1(k2_relat_1(k2_zfmisc_1(A_116, k2_zfmisc_1(A_397, B_396))), B_396) | ~v1_relat_1(k2_zfmisc_1(A_116, k2_zfmisc_1(A_397, B_396))))), inference(resolution, [status(thm)], [c_414, c_6447])).
% 9.61/3.39  tff(c_6466, plain, (![A_116, A_397, B_396]: (v5_relat_1(k2_relat_1(k2_zfmisc_1(A_116, k2_zfmisc_1(A_397, B_396))), B_396))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6453])).
% 9.61/3.39  tff(c_6581, plain, (![B_412, A_413]: (m1_subset_1(B_412, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_412), A_413))) | ~r1_tarski(k2_relat_1(B_412), A_413) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.61/3.39  tff(c_7692, plain, (![B_511]: (m1_subset_1(B_511, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_511), k1_xboole_0) | ~v1_funct_1(B_511) | ~v1_relat_1(B_511))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6581])).
% 9.61/3.39  tff(c_7698, plain, (![B_512]: (m1_subset_1(B_512, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(B_512) | ~v5_relat_1(B_512, k1_xboole_0) | ~v1_relat_1(B_512))), inference(resolution, [status(thm)], [c_38, c_7692])).
% 9.61/3.39  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.61/3.39  tff(c_8001, plain, (![B_517]: (r1_tarski(B_517, k1_xboole_0) | ~v1_funct_1(B_517) | ~v5_relat_1(B_517, k1_xboole_0) | ~v1_relat_1(B_517))), inference(resolution, [status(thm)], [c_7698, c_26])).
% 9.61/3.39  tff(c_8081, plain, (![A_116, A_397]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_116, k2_zfmisc_1(A_397, k1_xboole_0))), k1_xboole_0) | ~v1_funct_1(k2_relat_1(k2_zfmisc_1(A_116, k2_zfmisc_1(A_397, k1_xboole_0)))) | ~v1_relat_1(k2_relat_1(k2_zfmisc_1(A_116, k2_zfmisc_1(A_397, k1_xboole_0)))))), inference(resolution, [status(thm)], [c_6466, c_8001])).
% 9.61/3.39  tff(c_8145, plain, (r1_tarski(k2_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_534, c_22, c_22, c_22, c_22, c_22, c_22, c_8081])).
% 9.61/3.39  tff(c_8160, plain, (~v1_funct_1(k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8145])).
% 9.61/3.39  tff(c_377, plain, (![B_112, A_113]: (v1_funct_1(B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.61/3.39  tff(c_424, plain, (![A_120, B_121]: (v1_funct_1(A_120) | ~v1_funct_1(B_121) | ~v1_relat_1(B_121) | ~r1_tarski(A_120, B_121))), inference(resolution, [status(thm)], [c_28, c_377])).
% 9.61/3.39  tff(c_8232, plain, (![B_530, A_531]: (v1_funct_1(k2_relat_1(B_530)) | ~v1_funct_1(A_531) | ~v1_relat_1(A_531) | ~v5_relat_1(B_530, A_531) | ~v1_relat_1(B_530))), inference(resolution, [status(thm)], [c_38, c_424])).
% 9.61/3.39  tff(c_8278, plain, (![B_12]: (v1_funct_1(k2_relat_1(k1_xboole_0)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_418, c_8232])).
% 9.61/3.39  tff(c_8337, plain, (![B_12]: (v1_funct_1(k2_relat_1(k1_xboole_0)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_8278])).
% 9.61/3.39  tff(c_8347, plain, (![B_532]: (~v1_funct_1(B_532) | ~v1_relat_1(B_532))), inference(negUnitSimplification, [status(thm)], [c_8160, c_8337])).
% 9.61/3.39  tff(c_8407, plain, (~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_170, c_8347])).
% 9.61/3.39  tff(c_8436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_8407])).
% 9.61/3.39  tff(c_8437, plain, (r1_tarski(k2_relat_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_8145])).
% 9.61/3.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.39  tff(c_8465, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8437, c_2])).
% 9.61/3.39  tff(c_8488, plain, (~r1_tarski(k1_xboole_0, k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8465])).
% 9.61/3.39  tff(c_8770, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8764, c_8488])).
% 9.61/3.39  tff(c_8800, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8770])).
% 9.61/3.39  tff(c_8922, plain, (![B_553]: (k2_relat_1(k1_xboole_0)=k1_tarski(B_553))), inference(splitRight, [status(thm)], [c_8759])).
% 9.61/3.39  tff(c_8938, plain, (![B_553]: (~r1_tarski(k1_xboole_0, k1_tarski(B_553)))), inference(superposition, [status(thm), theory('equality')], [c_8922, c_8488])).
% 9.61/3.39  tff(c_9016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_8938])).
% 9.61/3.39  tff(c_9017, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_8465])).
% 9.61/3.39  tff(c_9096, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20) | ~v5_relat_1(k1_xboole_0, A_20) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9017, c_38])).
% 9.61/3.39  tff(c_9121, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_418, c_9096])).
% 9.61/3.39  tff(c_535, plain, (![B_132, A_133]: (k1_tarski(k1_funct_1(B_132, A_133))=k2_relat_1(B_132) | k1_tarski(A_133)!=k1_relat_1(B_132) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.61/3.39  tff(c_86, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 9.61/3.39  tff(c_550, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski('#skF_2')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_535, c_86])).
% 9.61/3.39  tff(c_558, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski('#skF_2')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_94, c_550])).
% 9.61/3.39  tff(c_6375, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_5')), inference(splitLeft, [status(thm)], [c_558])).
% 9.61/3.39  tff(c_271, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_90, c_257])).
% 9.61/3.39  tff(c_34, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.61/3.39  tff(c_9280, plain, (![B_565, B_566]: (k1_tarski(B_565)=k1_relat_1(B_566) | k1_relat_1(B_566)=k1_xboole_0 | ~v4_relat_1(B_566, k1_tarski(B_565)) | ~v1_relat_1(B_566))), inference(resolution, [status(thm)], [c_34, c_346])).
% 9.61/3.39  tff(c_9354, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_271, c_9280])).
% 9.61/3.39  tff(c_9390, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_9354])).
% 9.61/3.39  tff(c_9391, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6375, c_9390])).
% 9.61/3.39  tff(c_68, plain, (![B_44, A_43]: (m1_subset_1(B_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44), A_43))) | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.61/3.39  tff(c_9431, plain, (![A_43]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_43))) | ~r1_tarski(k2_relat_1('#skF_5'), A_43) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9391, c_68])).
% 9.61/3.39  tff(c_9472, plain, (![A_43]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_5'), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_94, c_24, c_9431])).
% 9.61/3.39  tff(c_9755, plain, (![A_571]: (~r1_tarski(k2_relat_1('#skF_5'), A_571))), inference(splitLeft, [status(thm)], [c_9472])).
% 9.61/3.39  tff(c_9767, plain, $false, inference(resolution, [status(thm)], [c_6, c_9755])).
% 9.61/3.39  tff(c_9768, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_9472])).
% 9.61/3.39  tff(c_9816, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_9768, c_26])).
% 9.61/3.39  tff(c_9872, plain, (k1_xboole_0='#skF_5' | ~r1_tarski(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_9816, c_2])).
% 9.61/3.39  tff(c_9883, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9121, c_9872])).
% 9.61/3.39  tff(c_9909, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_9883, c_9391])).
% 9.61/3.39  tff(c_226, plain, (![B_77, A_78]: (r1_tarski(k1_relat_1(B_77), A_78) | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.61/3.39  tff(c_570, plain, (![B_136, A_137]: (v1_relat_1(k1_relat_1(B_136)) | ~v1_relat_1(A_137) | ~v4_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_226, c_171])).
% 9.61/3.39  tff(c_572, plain, (![A_11]: (v1_relat_1(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(A_11) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_374, c_570])).
% 9.61/3.39  tff(c_583, plain, (![A_11]: (v1_relat_1(k1_relat_1(k1_xboole_0)) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_572])).
% 9.61/3.39  tff(c_592, plain, (![A_11]: (~v1_relat_1(A_11))), inference(splitLeft, [status(thm)], [c_583])).
% 9.61/3.39  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_592, c_534])).
% 9.61/3.39  tff(c_604, plain, (v1_relat_1(k1_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_583])).
% 9.61/3.39  tff(c_345, plain, (![A_105, B_106]: (v4_relat_1(k2_zfmisc_1(A_105, B_106), A_105))), inference(resolution, [status(thm)], [c_6, c_319])).
% 9.61/3.39  tff(c_6644, plain, (![B_421, B_422, A_423]: (v5_relat_1(k1_relat_1(B_421), B_422) | ~v4_relat_1(B_421, k2_zfmisc_1(A_423, B_422)) | ~v1_relat_1(B_421))), inference(resolution, [status(thm)], [c_34, c_388])).
% 9.61/3.39  tff(c_6650, plain, (![A_423, B_422, B_106]: (v5_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423, B_422), B_106)), B_422) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423, B_422), B_106)))), inference(resolution, [status(thm)], [c_345, c_6644])).
% 9.61/3.39  tff(c_6663, plain, (![A_423, B_422, B_106]: (v5_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423, B_422), B_106)), B_422))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6650])).
% 9.61/3.39  tff(c_8057, plain, (![A_423, B_106]: (r1_tarski(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423, k1_xboole_0), B_106)), k1_xboole_0) | ~v1_funct_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423, k1_xboole_0), B_106))) | ~v1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(A_423, k1_xboole_0), B_106))))), inference(resolution, [status(thm)], [c_6663, c_8001])).
% 9.61/3.39  tff(c_8133, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_24, c_22, c_24, c_22, c_24, c_22, c_8057])).
% 9.61/3.39  tff(c_8159, plain, (~v1_funct_1(k1_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8133])).
% 9.61/3.39  tff(c_9918, plain, (~v1_funct_1(k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_9883, c_8159])).
% 9.61/3.39  tff(c_10144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_9909, c_9918])).
% 9.61/3.39  tff(c_10146, plain, (v1_funct_1(k1_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_8133])).
% 9.61/3.39  tff(c_10171, plain, (~v1_funct_1(k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_8145])).
% 9.61/3.39  tff(c_10843, plain, (![B_603, A_604]: (v1_funct_1(k2_relat_1(B_603)) | ~v1_funct_1(A_604) | ~v1_relat_1(A_604) | ~v5_relat_1(B_603, A_604) | ~v1_relat_1(B_603))), inference(resolution, [status(thm)], [c_38, c_424])).
% 9.61/3.39  tff(c_10889, plain, (![B_12]: (v1_funct_1(k2_relat_1(k1_xboole_0)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_418, c_10843])).
% 9.61/3.39  tff(c_10954, plain, (![B_12]: (v1_funct_1(k2_relat_1(k1_xboole_0)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_10889])).
% 9.61/3.39  tff(c_10964, plain, (![B_605]: (~v1_funct_1(B_605) | ~v1_relat_1(B_605))), inference(negUnitSimplification, [status(thm)], [c_10171, c_10954])).
% 9.61/3.39  tff(c_11021, plain, (~v1_funct_1(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_604, c_10964])).
% 9.61/3.39  tff(c_11061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10146, c_11021])).
% 9.61/3.39  tff(c_11062, plain, (r1_tarski(k2_relat_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_8145])).
% 9.61/3.39  tff(c_11090, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_11062, c_2])).
% 9.61/3.39  tff(c_11116, plain, (~r1_tarski(k1_xboole_0, k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_11090])).
% 9.61/3.39  tff(c_11858, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11852, c_11116])).
% 9.61/3.39  tff(c_11888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_11858])).
% 9.61/3.39  tff(c_12007, plain, (![B_642]: (k2_relat_1(k1_xboole_0)=k1_tarski(B_642))), inference(splitRight, [status(thm)], [c_11847])).
% 9.61/3.39  tff(c_12023, plain, (![B_642]: (~r1_tarski(k1_xboole_0, k1_tarski(B_642)))), inference(superposition, [status(thm), theory('equality')], [c_12007, c_11116])).
% 9.61/3.39  tff(c_12101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_12023])).
% 9.61/3.39  tff(c_12102, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_11090])).
% 9.61/3.39  tff(c_12181, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20) | ~v5_relat_1(k1_xboole_0, A_20) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12102, c_38])).
% 9.61/3.39  tff(c_12206, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_418, c_12181])).
% 9.61/3.39  tff(c_10145, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_8133])).
% 9.61/3.39  tff(c_10167, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10145, c_2])).
% 9.61/3.39  tff(c_11115, plain, (~r1_tarski(k1_xboole_0, k1_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_10167])).
% 9.61/3.39  tff(c_12214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12206, c_11115])).
% 9.61/3.39  tff(c_12215, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_10167])).
% 9.61/3.39  tff(c_12312, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18) | ~v4_relat_1(k1_xboole_0, A_18) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12215, c_34])).
% 9.61/3.39  tff(c_12349, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_374, c_12312])).
% 9.61/3.39  tff(c_12879, plain, (![B_668, B_669]: (k1_tarski(B_668)=k1_relat_1(B_669) | k1_relat_1(B_669)=k1_xboole_0 | ~v4_relat_1(B_669, k1_tarski(B_668)) | ~v1_relat_1(B_669))), inference(resolution, [status(thm)], [c_34, c_346])).
% 9.61/3.39  tff(c_12921, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_271, c_12879])).
% 9.61/3.39  tff(c_12937, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_12921])).
% 9.61/3.39  tff(c_12938, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_6375, c_12937])).
% 9.61/3.39  tff(c_12978, plain, (![A_43]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_43))) | ~r1_tarski(k2_relat_1('#skF_5'), A_43) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12938, c_68])).
% 9.61/3.39  tff(c_13019, plain, (![A_43]: (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_5'), A_43))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_94, c_24, c_12978])).
% 9.61/3.39  tff(c_13102, plain, (![A_673]: (~r1_tarski(k2_relat_1('#skF_5'), A_673))), inference(splitLeft, [status(thm)], [c_13019])).
% 9.61/3.39  tff(c_13114, plain, $false, inference(resolution, [status(thm)], [c_6, c_13102])).
% 9.61/3.39  tff(c_13115, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_13019])).
% 9.61/3.39  tff(c_13163, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_13115, c_26])).
% 9.61/3.39  tff(c_13236, plain, (k1_xboole_0='#skF_5' | ~r1_tarski(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_13163, c_2])).
% 9.61/3.39  tff(c_13254, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12349, c_13236])).
% 9.61/3.39  tff(c_13276, plain, (![A_18]: (r1_tarski('#skF_5', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_13254, c_12349])).
% 9.61/3.39  tff(c_290, plain, (![C_90, B_12]: (v5_relat_1(C_90, B_12) | ~m1_subset_1(C_90, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_280])).
% 9.61/3.39  tff(c_13167, plain, (![B_676]: (v5_relat_1('#skF_5', B_676))), inference(resolution, [status(thm)], [c_13115, c_290])).
% 9.61/3.39  tff(c_12366, plain, (![A_646]: (r1_tarski(k1_xboole_0, A_646))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_374, c_12312])).
% 9.61/3.39  tff(c_245, plain, (![B_80, A_81]: (k2_relat_1(B_80)=A_81 | ~r1_tarski(A_81, k2_relat_1(B_80)) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_239, c_2])).
% 9.61/3.39  tff(c_12401, plain, (![B_80]: (k2_relat_1(B_80)=k1_xboole_0 | ~v5_relat_1(B_80, k1_xboole_0) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_12366, c_245])).
% 9.61/3.39  tff(c_13175, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_13167, c_12401])).
% 9.61/3.39  tff(c_13200, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_170, c_13175])).
% 9.61/3.39  tff(c_13486, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13254, c_13200])).
% 9.61/3.39  tff(c_192, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.61/3.39  tff(c_202, plain, (![B_25, A_24]: (k9_relat_1(B_25, A_24)=k2_relat_1(B_25) | ~r1_tarski(k2_relat_1(B_25), k9_relat_1(B_25, A_24)) | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_42, c_192])).
% 9.61/3.39  tff(c_13490, plain, (![A_24]: (k9_relat_1('#skF_5', A_24)=k2_relat_1('#skF_5') | ~r1_tarski('#skF_5', k9_relat_1('#skF_5', A_24)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_13486, c_202])).
% 9.61/3.39  tff(c_13509, plain, (![A_24]: (k9_relat_1('#skF_5', A_24)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_13276, c_13486, c_13490])).
% 9.61/3.39  tff(c_6515, plain, (![A_402, B_403, C_404, D_405]: (k7_relset_1(A_402, B_403, C_404, D_405)=k9_relat_1(C_404, D_405) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.61/3.39  tff(c_6525, plain, (![D_405]: (k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', D_405)=k9_relat_1('#skF_5', D_405))), inference(resolution, [status(thm)], [c_90, c_6515])).
% 9.61/3.39  tff(c_6547, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6525, c_86])).
% 9.61/3.39  tff(c_13747, plain, (~r1_tarski('#skF_5', k1_tarski(k1_funct_1('#skF_5', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13509, c_6547])).
% 9.61/3.39  tff(c_13751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13276, c_13747])).
% 9.61/3.39  tff(c_13753, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_558])).
% 9.61/3.39  tff(c_13772, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_13753, c_90])).
% 9.61/3.39  tff(c_54, plain, (![A_36, B_37, C_38, D_39]: (k7_relset_1(A_36, B_37, C_38, D_39)=k9_relat_1(C_38, D_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.61/3.39  tff(c_13865, plain, (![D_39]: (k7_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5', D_39)=k9_relat_1('#skF_5', D_39))), inference(resolution, [status(thm)], [c_13772, c_54])).
% 9.61/3.39  tff(c_13752, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_558])).
% 9.61/3.39  tff(c_13936, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_5'), '#skF_3', '#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_13753, c_13752])).
% 9.61/3.39  tff(c_13950, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_13865, c_13936])).
% 9.61/3.39  tff(c_13963, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_13950])).
% 9.61/3.39  tff(c_13967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_13963])).
% 9.61/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.61/3.39  
% 9.61/3.39  Inference rules
% 9.61/3.39  ----------------------
% 9.61/3.39  #Ref     : 0
% 9.61/3.39  #Sup     : 2696
% 9.61/3.39  #Fact    : 0
% 9.61/3.39  #Define  : 0
% 9.61/3.39  #Split   : 89
% 9.61/3.39  #Chain   : 0
% 9.61/3.39  #Close   : 0
% 9.61/3.39  
% 9.61/3.39  Ordering : KBO
% 9.61/3.39  
% 9.61/3.39  Simplification rules
% 9.61/3.39  ----------------------
% 9.61/3.39  #Subsume      : 1275
% 9.61/3.39  #Demod        : 3302
% 9.61/3.39  #Tautology    : 996
% 9.61/3.39  #SimpNegUnit  : 556
% 9.61/3.39  #BackRed      : 892
% 9.61/3.39  
% 9.61/3.39  #Partial instantiations: 0
% 9.61/3.39  #Strategies tried      : 1
% 9.61/3.39  
% 9.61/3.39  Timing (in seconds)
% 9.61/3.39  ----------------------
% 9.61/3.39  Preprocessing        : 0.38
% 9.61/3.39  Parsing              : 0.20
% 9.61/3.39  CNF conversion       : 0.03
% 9.61/3.39  Main loop            : 2.17
% 9.61/3.39  Inferencing          : 0.60
% 9.61/3.39  Reduction            : 0.85
% 9.61/3.39  Demodulation         : 0.62
% 9.61/3.39  BG Simplification    : 0.08
% 9.61/3.39  Subsumption          : 0.46
% 9.61/3.39  Abstraction          : 0.10
% 9.61/3.39  MUC search           : 0.00
% 9.61/3.39  Cooper               : 0.00
% 9.61/3.39  Total                : 2.61
% 9.61/3.39  Index Insertion      : 0.00
% 9.61/3.39  Index Deletion       : 0.00
% 9.61/3.39  Index Matching       : 0.00
% 9.61/3.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
