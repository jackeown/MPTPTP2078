%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:26 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 777 expanded)
%              Number of leaves         :   48 ( 273 expanded)
%              Depth                    :   14
%              Number of atoms          :  247 (1662 expanded)
%              Number of equality atoms :   79 ( 357 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_114,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_130,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_186,plain,(
    ! [B_89,A_90] :
      ( ~ r1_xboole_0(B_89,A_90)
      | ~ r1_tarski(B_89,A_90)
      | v1_xboole_0(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_192,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_186])).

tff(c_196,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_192])).

tff(c_24,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3462,plain,(
    ! [C_368,B_369,A_370] :
      ( ~ v1_xboole_0(C_368)
      | ~ m1_subset_1(B_369,k1_zfmisc_1(C_368))
      | ~ r2_hidden(A_370,B_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3525,plain,(
    ! [B_375,A_376,A_377] :
      ( ~ v1_xboole_0(B_375)
      | ~ r2_hidden(A_376,A_377)
      | ~ r1_tarski(A_377,B_375) ) ),
    inference(resolution,[status(thm)],[c_36,c_3462])).

tff(c_3532,plain,(
    ! [B_378,A_379] :
      ( ~ v1_xboole_0(B_378)
      | ~ r1_tarski(A_379,B_378)
      | k1_xboole_0 = A_379 ) ),
    inference(resolution,[status(thm)],[c_16,c_3525])).

tff(c_3553,plain,(
    ! [A_380,B_381] :
      ( ~ v1_xboole_0(A_380)
      | k3_xboole_0(A_380,B_381) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_3532])).

tff(c_3558,plain,(
    ! [B_381] : k3_xboole_0(k1_xboole_0,B_381) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_3553])).

tff(c_152,plain,(
    ! [A_82,B_83] :
      ( r1_xboole_0(A_82,B_83)
      | k3_xboole_0(A_82,B_83) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_xboole_0(B_10,A_9)
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,(
    ! [B_83,A_82] :
      ( r1_xboole_0(B_83,A_82)
      | k3_xboole_0(A_82,B_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152,c_14])).

tff(c_48,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3239,plain,(
    ! [B_324,A_325] :
      ( v1_relat_1(B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_325))
      | ~ v1_relat_1(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3249,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_3239])).

tff(c_3254,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3249])).

tff(c_3561,plain,(
    ! [B_382] : k3_xboole_0(k1_xboole_0,B_382) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_3553])).

tff(c_3222,plain,(
    ! [B_322,A_323] :
      ( r1_xboole_0(B_322,A_323)
      | k3_xboole_0(A_323,B_322) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152,c_14])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3236,plain,(
    ! [B_322,A_323] :
      ( k3_xboole_0(B_322,A_323) = k1_xboole_0
      | k3_xboole_0(A_323,B_322) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3222,c_8])).

tff(c_3652,plain,(
    ! [B_387] : k3_xboole_0(B_387,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3561,c_3236])).

tff(c_3672,plain,(
    ! [B_387] : r1_tarski(k1_xboole_0,B_387) ),
    inference(superposition,[status(thm),theory(equality)],[c_3652,c_24])).

tff(c_411,plain,(
    ! [C_129,B_130,A_131] :
      ( ~ v1_xboole_0(C_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(C_129))
      | ~ r2_hidden(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_427,plain,(
    ! [B_132,A_133,A_134] :
      ( ~ v1_xboole_0(B_132)
      | ~ r2_hidden(A_133,A_134)
      | ~ r1_tarski(A_134,B_132) ) ),
    inference(resolution,[status(thm)],[c_36,c_411])).

tff(c_435,plain,(
    ! [B_135,A_136] :
      ( ~ v1_xboole_0(B_135)
      | ~ r1_tarski(A_136,B_135)
      | k1_xboole_0 = A_136 ) ),
    inference(resolution,[status(thm)],[c_16,c_427])).

tff(c_452,plain,(
    ! [A_137,B_138] :
      ( ~ v1_xboole_0(A_137)
      | k3_xboole_0(A_137,B_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_435])).

tff(c_457,plain,(
    ! [B_138] : k3_xboole_0(k1_xboole_0,B_138) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_452])).

tff(c_239,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_249,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_239])).

tff(c_254,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_249])).

tff(c_339,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_358,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_339])).

tff(c_44,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_relat_1(B_31),A_30)
      | ~ v4_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_332,plain,(
    ! [C_113,B_114,A_115] :
      ( r2_hidden(C_113,B_114)
      | ~ r2_hidden(C_113,A_115)
      | ~ r1_tarski(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1392,plain,(
    ! [A_214,B_215] :
      ( r2_hidden('#skF_2'(A_214),B_215)
      | ~ r1_tarski(A_214,B_215)
      | k1_xboole_0 = A_214 ) ),
    inference(resolution,[status(thm)],[c_16,c_332])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2970,plain,(
    ! [A_317,B_318] :
      ( m1_subset_1('#skF_2'(A_317),B_318)
      | ~ r1_tarski(A_317,B_318)
      | k1_xboole_0 = A_317 ) ),
    inference(resolution,[status(thm)],[c_1392,c_32])).

tff(c_841,plain,(
    ! [A_162,B_163,C_164] :
      ( k1_relset_1(A_162,B_163,C_164) = k1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_860,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_841])).

tff(c_137,plain,(
    ! [D_80] :
      ( ~ r2_hidden(D_80,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_80,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_142,plain,
    ( ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_137])).

tff(c_220,plain,(
    ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_862,plain,(
    ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_220])).

tff(c_3044,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2970,c_862])).

tff(c_3052,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3044])).

tff(c_3105,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_3052])).

tff(c_3111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_358,c_3105])).

tff(c_3112,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3044])).

tff(c_52,plain,(
    ! [B_39,A_38] :
      ( k7_relat_1(B_39,A_38) = B_39
      | ~ v4_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_361,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_358,c_52])).

tff(c_364,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_361])).

tff(c_696,plain,(
    ! [C_155,A_156,B_157] :
      ( k7_relat_1(k7_relat_1(C_155,A_156),B_157) = k1_xboole_0
      | ~ r1_xboole_0(A_156,B_157)
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_721,plain,(
    ! [B_157] :
      ( k7_relat_1('#skF_5',B_157) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_157)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_696])).

tff(c_739,plain,(
    ! [B_158] :
      ( k7_relat_1('#skF_5',B_158) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_721])).

tff(c_1702,plain,(
    ! [A_245] :
      ( k7_relat_1('#skF_5',A_245) = k1_xboole_0
      | k3_xboole_0(A_245,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_163,c_739])).

tff(c_54,plain,(
    ! [A_40] :
      ( k7_relat_1(A_40,k1_relat_1(A_40)) = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1718,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ v1_relat_1('#skF_5')
    | k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_54])).

tff(c_1737,plain,
    ( k1_xboole_0 = '#skF_5'
    | k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_1718])).

tff(c_1742,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_3119,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3112,c_1742])).

tff(c_3130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_3119])).

tff(c_3131,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_941,plain,(
    ! [A_170,B_171,C_172] :
      ( k2_relset_1(A_170,B_171,C_172) = k2_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_960,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_941])).

tff(c_66,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_961,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_66])).

tff(c_3153,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_961])).

tff(c_77,plain,(
    ! [A_66] :
      ( v1_xboole_0(k2_relat_1(A_66))
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [A_66] :
      ( k2_relat_1(A_66) = k1_xboole_0
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_77,c_12])).

tff(c_203,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_196,c_81])).

tff(c_3176,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3131,c_3131,c_203])).

tff(c_3207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3153,c_3176])).

tff(c_3208,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_3584,plain,(
    ! [A_383,B_384,C_385] :
      ( k1_relset_1(A_383,B_384,C_385) = k1_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3599,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3584])).

tff(c_3604,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3208,c_3599])).

tff(c_42,plain,(
    ! [B_31,A_30] :
      ( v4_relat_1(B_31,A_30)
      | ~ r1_tarski(k1_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3611,plain,(
    ! [A_30] :
      ( v4_relat_1('#skF_5',A_30)
      | ~ r1_tarski(k1_xboole_0,A_30)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3604,c_42])).

tff(c_3623,plain,(
    ! [A_30] :
      ( v4_relat_1('#skF_5',A_30)
      | ~ r1_tarski(k1_xboole_0,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_3611])).

tff(c_3715,plain,(
    ! [A_390] : v4_relat_1('#skF_5',A_390) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3623])).

tff(c_3718,plain,(
    ! [A_390] :
      ( k7_relat_1('#skF_5',A_390) = '#skF_5'
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3715,c_52])).

tff(c_3721,plain,(
    ! [A_390] : k7_relat_1('#skF_5',A_390) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_3718])).

tff(c_3341,plain,(
    ! [C_345,A_346,B_347] :
      ( v4_relat_1(C_345,A_346)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3360,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_3341])).

tff(c_3361,plain,(
    ! [B_348,A_349] :
      ( k7_relat_1(B_348,A_349) = B_348
      | ~ v4_relat_1(B_348,A_349)
      | ~ v1_relat_1(B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3364,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3360,c_3361])).

tff(c_3367,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_3364])).

tff(c_3478,plain,(
    ! [C_371,A_372,B_373] :
      ( k7_relat_1(k7_relat_1(C_371,A_372),B_373) = k1_xboole_0
      | ~ r1_xboole_0(A_372,B_373)
      | ~ v1_relat_1(C_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3500,plain,(
    ! [B_373] :
      ( k7_relat_1('#skF_5',B_373) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_373)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3367,c_3478])).

tff(c_3513,plain,(
    ! [B_373] :
      ( k7_relat_1('#skF_5',B_373) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_3500])).

tff(c_3757,plain,(
    ! [B_373] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r1_xboole_0('#skF_4',B_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3721,c_3513])).

tff(c_3847,plain,(
    ! [B_400] : ~ r1_xboole_0('#skF_4',B_400) ),
    inference(splitLeft,[status(thm)],[c_3757])).

tff(c_3858,plain,(
    ! [A_401] : k3_xboole_0(A_401,'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_3847])).

tff(c_3863,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3558,c_3858])).

tff(c_3864,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3757])).

tff(c_3722,plain,(
    ! [A_391,B_392,C_393] :
      ( k2_relset_1(A_391,B_392,C_393) = k2_relat_1(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3741,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3722])).

tff(c_3750,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3741,c_66])).

tff(c_3868,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_3750])).

tff(c_3884,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_3864,c_203])).

tff(c_3978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3868,c_3884])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.93  
% 5.14/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.93  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.14/1.93  
% 5.14/1.93  %Foreground sorts:
% 5.14/1.93  
% 5.14/1.93  
% 5.14/1.93  %Background operators:
% 5.14/1.93  
% 5.14/1.93  
% 5.14/1.93  %Foreground operators:
% 5.14/1.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.14/1.93  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.14/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/1.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.14/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.14/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.14/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.14/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.14/1.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.14/1.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.14/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.14/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.14/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.14/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/1.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.14/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.14/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.14/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.14/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.14/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.14/1.93  
% 5.14/1.95  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/1.95  tff(f_72, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.14/1.95  tff(f_80, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.14/1.95  tff(f_60, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.14/1.95  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.14/1.95  tff(f_88, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.14/1.95  tff(f_95, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.14/1.95  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.14/1.95  tff(f_44, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.14/1.95  tff(f_114, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.14/1.95  tff(f_165, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 5.14/1.95  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.14/1.95  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.14/1.95  tff(f_108, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.14/1.95  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.14/1.95  tff(f_84, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.14/1.95  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.14/1.95  tff(f_126, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.14/1.95  tff(f_120, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 5.14/1.95  tff(f_130, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 5.14/1.95  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.14/1.95  tff(f_112, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 5.14/1.95  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.14/1.95  tff(c_22, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.14/1.95  tff(c_26, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.14/1.95  tff(c_186, plain, (![B_89, A_90]: (~r1_xboole_0(B_89, A_90) | ~r1_tarski(B_89, A_90) | v1_xboole_0(B_89))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.14/1.95  tff(c_192, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_186])).
% 5.14/1.95  tff(c_196, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_192])).
% 5.14/1.95  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.14/1.95  tff(c_16, plain, (![A_11]: (r2_hidden('#skF_2'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/1.95  tff(c_36, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.14/1.95  tff(c_3462, plain, (![C_368, B_369, A_370]: (~v1_xboole_0(C_368) | ~m1_subset_1(B_369, k1_zfmisc_1(C_368)) | ~r2_hidden(A_370, B_369))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/1.95  tff(c_3525, plain, (![B_375, A_376, A_377]: (~v1_xboole_0(B_375) | ~r2_hidden(A_376, A_377) | ~r1_tarski(A_377, B_375))), inference(resolution, [status(thm)], [c_36, c_3462])).
% 5.14/1.95  tff(c_3532, plain, (![B_378, A_379]: (~v1_xboole_0(B_378) | ~r1_tarski(A_379, B_378) | k1_xboole_0=A_379)), inference(resolution, [status(thm)], [c_16, c_3525])).
% 5.14/1.95  tff(c_3553, plain, (![A_380, B_381]: (~v1_xboole_0(A_380) | k3_xboole_0(A_380, B_381)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_3532])).
% 5.14/1.95  tff(c_3558, plain, (![B_381]: (k3_xboole_0(k1_xboole_0, B_381)=k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_3553])).
% 5.14/1.95  tff(c_152, plain, (![A_82, B_83]: (r1_xboole_0(A_82, B_83) | k3_xboole_0(A_82, B_83)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.14/1.95  tff(c_14, plain, (![B_10, A_9]: (r1_xboole_0(B_10, A_9) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.14/1.95  tff(c_163, plain, (![B_83, A_82]: (r1_xboole_0(B_83, A_82) | k3_xboole_0(A_82, B_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_152, c_14])).
% 5.14/1.95  tff(c_48, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.14/1.95  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.14/1.95  tff(c_3239, plain, (![B_324, A_325]: (v1_relat_1(B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(A_325)) | ~v1_relat_1(A_325))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.14/1.95  tff(c_3249, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_3239])).
% 5.14/1.95  tff(c_3254, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3249])).
% 5.14/1.95  tff(c_3561, plain, (![B_382]: (k3_xboole_0(k1_xboole_0, B_382)=k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_3553])).
% 5.14/1.95  tff(c_3222, plain, (![B_322, A_323]: (r1_xboole_0(B_322, A_323) | k3_xboole_0(A_323, B_322)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_152, c_14])).
% 5.14/1.95  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.14/1.95  tff(c_3236, plain, (![B_322, A_323]: (k3_xboole_0(B_322, A_323)=k1_xboole_0 | k3_xboole_0(A_323, B_322)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3222, c_8])).
% 5.14/1.95  tff(c_3652, plain, (![B_387]: (k3_xboole_0(B_387, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3561, c_3236])).
% 5.14/1.95  tff(c_3672, plain, (![B_387]: (r1_tarski(k1_xboole_0, B_387))), inference(superposition, [status(thm), theory('equality')], [c_3652, c_24])).
% 5.14/1.95  tff(c_411, plain, (![C_129, B_130, A_131]: (~v1_xboole_0(C_129) | ~m1_subset_1(B_130, k1_zfmisc_1(C_129)) | ~r2_hidden(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.14/1.95  tff(c_427, plain, (![B_132, A_133, A_134]: (~v1_xboole_0(B_132) | ~r2_hidden(A_133, A_134) | ~r1_tarski(A_134, B_132))), inference(resolution, [status(thm)], [c_36, c_411])).
% 5.14/1.95  tff(c_435, plain, (![B_135, A_136]: (~v1_xboole_0(B_135) | ~r1_tarski(A_136, B_135) | k1_xboole_0=A_136)), inference(resolution, [status(thm)], [c_16, c_427])).
% 5.14/1.95  tff(c_452, plain, (![A_137, B_138]: (~v1_xboole_0(A_137) | k3_xboole_0(A_137, B_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_435])).
% 5.14/1.95  tff(c_457, plain, (![B_138]: (k3_xboole_0(k1_xboole_0, B_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_196, c_452])).
% 5.14/1.95  tff(c_239, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.14/1.95  tff(c_249, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_239])).
% 5.14/1.95  tff(c_254, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_249])).
% 5.14/1.95  tff(c_339, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.14/1.95  tff(c_358, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_339])).
% 5.14/1.95  tff(c_44, plain, (![B_31, A_30]: (r1_tarski(k1_relat_1(B_31), A_30) | ~v4_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.14/1.95  tff(c_332, plain, (![C_113, B_114, A_115]: (r2_hidden(C_113, B_114) | ~r2_hidden(C_113, A_115) | ~r1_tarski(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.14/1.95  tff(c_1392, plain, (![A_214, B_215]: (r2_hidden('#skF_2'(A_214), B_215) | ~r1_tarski(A_214, B_215) | k1_xboole_0=A_214)), inference(resolution, [status(thm)], [c_16, c_332])).
% 5.14/1.95  tff(c_32, plain, (![A_20, B_21]: (m1_subset_1(A_20, B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.14/1.95  tff(c_2970, plain, (![A_317, B_318]: (m1_subset_1('#skF_2'(A_317), B_318) | ~r1_tarski(A_317, B_318) | k1_xboole_0=A_317)), inference(resolution, [status(thm)], [c_1392, c_32])).
% 5.14/1.95  tff(c_841, plain, (![A_162, B_163, C_164]: (k1_relset_1(A_162, B_163, C_164)=k1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.14/1.95  tff(c_860, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_841])).
% 5.14/1.95  tff(c_137, plain, (![D_80]: (~r2_hidden(D_80, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_80, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.14/1.95  tff(c_142, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_137])).
% 5.14/1.95  tff(c_220, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_142])).
% 5.14/1.95  tff(c_862, plain, (~m1_subset_1('#skF_2'(k1_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_220])).
% 5.14/1.95  tff(c_3044, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2970, c_862])).
% 5.14/1.95  tff(c_3052, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3044])).
% 5.14/1.95  tff(c_3105, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_3052])).
% 5.14/1.95  tff(c_3111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_358, c_3105])).
% 5.14/1.95  tff(c_3112, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3044])).
% 5.14/1.95  tff(c_52, plain, (![B_39, A_38]: (k7_relat_1(B_39, A_38)=B_39 | ~v4_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.14/1.95  tff(c_361, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_358, c_52])).
% 5.14/1.95  tff(c_364, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_361])).
% 5.14/1.95  tff(c_696, plain, (![C_155, A_156, B_157]: (k7_relat_1(k7_relat_1(C_155, A_156), B_157)=k1_xboole_0 | ~r1_xboole_0(A_156, B_157) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.14/1.95  tff(c_721, plain, (![B_157]: (k7_relat_1('#skF_5', B_157)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_157) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_364, c_696])).
% 5.14/1.95  tff(c_739, plain, (![B_158]: (k7_relat_1('#skF_5', B_158)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_158))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_721])).
% 5.14/1.95  tff(c_1702, plain, (![A_245]: (k7_relat_1('#skF_5', A_245)=k1_xboole_0 | k3_xboole_0(A_245, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_163, c_739])).
% 5.14/1.95  tff(c_54, plain, (![A_40]: (k7_relat_1(A_40, k1_relat_1(A_40))=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.14/1.95  tff(c_1718, plain, (k1_xboole_0='#skF_5' | ~v1_relat_1('#skF_5') | k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1702, c_54])).
% 5.14/1.95  tff(c_1737, plain, (k1_xboole_0='#skF_5' | k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_254, c_1718])).
% 5.14/1.95  tff(c_1742, plain, (k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1737])).
% 5.14/1.95  tff(c_3119, plain, (k3_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3112, c_1742])).
% 5.14/1.95  tff(c_3130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_457, c_3119])).
% 5.14/1.95  tff(c_3131, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1737])).
% 5.14/1.95  tff(c_941, plain, (![A_170, B_171, C_172]: (k2_relset_1(A_170, B_171, C_172)=k2_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.14/1.95  tff(c_960, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_941])).
% 5.14/1.95  tff(c_66, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.14/1.95  tff(c_961, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_960, c_66])).
% 5.14/1.95  tff(c_3153, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_961])).
% 5.14/1.95  tff(c_77, plain, (![A_66]: (v1_xboole_0(k2_relat_1(A_66)) | ~v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.14/1.95  tff(c_12, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.14/1.95  tff(c_81, plain, (![A_66]: (k2_relat_1(A_66)=k1_xboole_0 | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_77, c_12])).
% 5.14/1.95  tff(c_203, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_196, c_81])).
% 5.14/1.95  tff(c_3176, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3131, c_3131, c_203])).
% 5.14/1.95  tff(c_3207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3153, c_3176])).
% 5.14/1.95  tff(c_3208, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_142])).
% 5.14/1.95  tff(c_3584, plain, (![A_383, B_384, C_385]: (k1_relset_1(A_383, B_384, C_385)=k1_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.14/1.95  tff(c_3599, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_3584])).
% 5.14/1.95  tff(c_3604, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3208, c_3599])).
% 5.14/1.95  tff(c_42, plain, (![B_31, A_30]: (v4_relat_1(B_31, A_30) | ~r1_tarski(k1_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.14/1.95  tff(c_3611, plain, (![A_30]: (v4_relat_1('#skF_5', A_30) | ~r1_tarski(k1_xboole_0, A_30) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3604, c_42])).
% 5.14/1.95  tff(c_3623, plain, (![A_30]: (v4_relat_1('#skF_5', A_30) | ~r1_tarski(k1_xboole_0, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_3611])).
% 5.14/1.95  tff(c_3715, plain, (![A_390]: (v4_relat_1('#skF_5', A_390))), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3623])).
% 5.14/1.95  tff(c_3718, plain, (![A_390]: (k7_relat_1('#skF_5', A_390)='#skF_5' | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3715, c_52])).
% 5.14/1.95  tff(c_3721, plain, (![A_390]: (k7_relat_1('#skF_5', A_390)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_3718])).
% 5.14/1.95  tff(c_3341, plain, (![C_345, A_346, B_347]: (v4_relat_1(C_345, A_346) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.14/1.95  tff(c_3360, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_3341])).
% 5.14/1.95  tff(c_3361, plain, (![B_348, A_349]: (k7_relat_1(B_348, A_349)=B_348 | ~v4_relat_1(B_348, A_349) | ~v1_relat_1(B_348))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.14/1.95  tff(c_3364, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3360, c_3361])).
% 5.14/1.95  tff(c_3367, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_3364])).
% 5.14/1.95  tff(c_3478, plain, (![C_371, A_372, B_373]: (k7_relat_1(k7_relat_1(C_371, A_372), B_373)=k1_xboole_0 | ~r1_xboole_0(A_372, B_373) | ~v1_relat_1(C_371))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.14/1.95  tff(c_3500, plain, (![B_373]: (k7_relat_1('#skF_5', B_373)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_373) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3367, c_3478])).
% 5.14/1.95  tff(c_3513, plain, (![B_373]: (k7_relat_1('#skF_5', B_373)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_373))), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_3500])).
% 5.14/1.95  tff(c_3757, plain, (![B_373]: (k1_xboole_0='#skF_5' | ~r1_xboole_0('#skF_4', B_373))), inference(demodulation, [status(thm), theory('equality')], [c_3721, c_3513])).
% 5.14/1.95  tff(c_3847, plain, (![B_400]: (~r1_xboole_0('#skF_4', B_400))), inference(splitLeft, [status(thm)], [c_3757])).
% 5.14/1.95  tff(c_3858, plain, (![A_401]: (k3_xboole_0(A_401, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_163, c_3847])).
% 5.14/1.95  tff(c_3863, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3558, c_3858])).
% 5.14/1.95  tff(c_3864, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3757])).
% 5.14/1.95  tff(c_3722, plain, (![A_391, B_392, C_393]: (k2_relset_1(A_391, B_392, C_393)=k2_relat_1(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.14/1.95  tff(c_3741, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_3722])).
% 5.14/1.95  tff(c_3750, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3741, c_66])).
% 5.14/1.95  tff(c_3868, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_3750])).
% 5.14/1.95  tff(c_3884, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3864, c_3864, c_203])).
% 5.14/1.95  tff(c_3978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3868, c_3884])).
% 5.14/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.95  
% 5.14/1.95  Inference rules
% 5.14/1.95  ----------------------
% 5.14/1.95  #Ref     : 0
% 5.14/1.95  #Sup     : 839
% 5.14/1.95  #Fact    : 0
% 5.14/1.95  #Define  : 0
% 5.14/1.95  #Split   : 19
% 5.14/1.95  #Chain   : 0
% 5.14/1.95  #Close   : 0
% 5.14/1.95  
% 5.14/1.95  Ordering : KBO
% 5.14/1.95  
% 5.14/1.95  Simplification rules
% 5.14/1.95  ----------------------
% 5.14/1.95  #Subsume      : 160
% 5.14/1.95  #Demod        : 499
% 5.14/1.95  #Tautology    : 359
% 5.14/1.95  #SimpNegUnit  : 16
% 5.14/1.95  #BackRed      : 116
% 5.14/1.95  
% 5.14/1.95  #Partial instantiations: 0
% 5.14/1.95  #Strategies tried      : 1
% 5.14/1.95  
% 5.14/1.95  Timing (in seconds)
% 5.14/1.95  ----------------------
% 5.14/1.96  Preprocessing        : 0.35
% 5.14/1.96  Parsing              : 0.19
% 5.14/1.96  CNF conversion       : 0.02
% 5.14/1.96  Main loop            : 0.83
% 5.14/1.96  Inferencing          : 0.28
% 5.14/1.96  Reduction            : 0.27
% 5.14/1.96  Demodulation         : 0.17
% 5.14/1.96  BG Simplification    : 0.03
% 5.14/1.96  Subsumption          : 0.17
% 5.14/1.96  Abstraction          : 0.04
% 5.14/1.96  MUC search           : 0.00
% 5.14/1.96  Cooper               : 0.00
% 5.14/1.96  Total                : 1.22
% 5.14/1.96  Index Insertion      : 0.00
% 5.14/1.96  Index Deletion       : 0.00
% 5.14/1.96  Index Matching       : 0.00
% 5.14/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
