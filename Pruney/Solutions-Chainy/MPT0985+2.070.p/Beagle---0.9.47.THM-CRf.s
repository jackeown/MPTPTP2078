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
% DateTime   : Thu Dec  3 10:12:37 EST 2020

% Result     : Theorem 14.74s
% Output     : CNFRefutation 15.12s
% Verified   : 
% Statistics : Number of formulae       :  333 (10915 expanded)
%              Number of leaves         :   44 (3433 expanded)
%              Depth                    :   21
%              Number of atoms          :  521 (27340 expanded)
%              Number of equality atoms :  184 (6688 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_153,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_143,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_130,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_464,plain,(
    ! [B_90,A_91] :
      ( v1_xboole_0(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_478,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_464])).

tff(c_510,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_514,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_510])).

tff(c_88,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_30,plain,(
    ! [A_20] :
      ( v1_funct_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_237,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_240,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_237])).

tff(c_243,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_240])).

tff(c_352,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_363,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_352])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_363])).

tff(c_375,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_539,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_712,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_731,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_712])).

tff(c_82,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_80,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1121,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1133,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1121])).

tff(c_1143,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1133])).

tff(c_36,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_376,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_28,plain,(
    ! [A_19] :
      ( k2_relat_1(A_19) = k1_xboole_0
      | k1_relat_1(A_19) != k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_738,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_731,c_28])).

tff(c_758,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_738])).

tff(c_26,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) = k1_xboole_0
      | k2_relat_1(A_19) != k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_739,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_731,c_26])).

tff(c_781,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_758,c_739])).

tff(c_1144,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_781])).

tff(c_86,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1250,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1279,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1250])).

tff(c_2440,plain,(
    ! [B_179,A_180,C_181] :
      ( k1_xboole_0 = B_179
      | k1_relset_1(A_180,B_179,C_181) = A_180
      | ~ v1_funct_2(C_181,A_180,B_179)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_180,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2461,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_2440])).

tff(c_2480,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1279,c_2461])).

tff(c_2481,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1144,c_2480])).

tff(c_871,plain,(
    ! [A_120] :
      ( k2_relat_1(k2_funct_1(A_120)) = k1_relat_1(A_120)
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    ! [A_38] :
      ( v1_funct_2(A_38,k1_relat_1(A_38),k2_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_21427,plain,(
    ! [A_550] :
      ( v1_funct_2(k2_funct_1(A_550),k1_relat_1(k2_funct_1(A_550)),k1_relat_1(A_550))
      | ~ v1_funct_1(k2_funct_1(A_550))
      | ~ v1_relat_1(k2_funct_1(A_550))
      | ~ v2_funct_1(A_550)
      | ~ v1_funct_1(A_550)
      | ~ v1_relat_1(A_550) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_74])).

tff(c_21481,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2481,c_21427])).

tff(c_21526,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_88,c_82,c_376,c_21481])).

tff(c_22119,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_21526])).

tff(c_22122,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_22119])).

tff(c_22126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_88,c_22122])).

tff(c_22128,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_21526])).

tff(c_34,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1173,plain,(
    ! [A_133] :
      ( m1_subset_1(A_133,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_133),k2_relat_1(A_133))))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_25506,plain,(
    ! [A_589] :
      ( m1_subset_1(k2_funct_1(A_589),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_589)),k1_relat_1(A_589))))
      | ~ v1_funct_1(k2_funct_1(A_589))
      | ~ v1_relat_1(k2_funct_1(A_589))
      | ~ v2_funct_1(A_589)
      | ~ v1_funct_1(A_589)
      | ~ v1_relat_1(A_589) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1173])).

tff(c_25589,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2481,c_25506])).

tff(c_25647,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_88,c_82,c_22128,c_376,c_25589])).

tff(c_25672,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'),'#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_25647])).

tff(c_25687,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_88,c_82,c_1143,c_25672])).

tff(c_25689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_25687])).

tff(c_25690,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_738])).

tff(c_26281,plain,(
    ! [A_612,B_613,C_614] :
      ( k2_relset_1(A_612,B_613,C_614) = k2_relat_1(C_614)
      | ~ m1_subset_1(C_614,k1_zfmisc_1(k2_zfmisc_1(A_612,B_613))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26296,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_26281])).

tff(c_26306,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25690,c_80,c_26296])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26344,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26306,c_6])).

tff(c_16,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26341,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26306,c_26306,c_16])).

tff(c_26472,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26341,c_510])).

tff(c_26476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26344,c_26472])).

tff(c_26478,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_20,plain,(
    ! [B_14,A_12] :
      ( v1_xboole_0(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26541,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26478,c_20])).

tff(c_26547,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26541])).

tff(c_26551,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_26547])).

tff(c_26663,plain,(
    ! [C_636,A_637,B_638] :
      ( v1_relat_1(C_636)
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(A_637,B_638))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26686,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_26663])).

tff(c_28061,plain,(
    ! [A_694,B_695,C_696] :
      ( k2_relset_1(A_694,B_695,C_696) = k2_relat_1(C_696)
      | ~ m1_subset_1(C_696,k1_zfmisc_1(k2_zfmisc_1(A_694,B_695))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28082,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_28061])).

tff(c_28094,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_28082])).

tff(c_26477,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_26693,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26686,c_28])).

tff(c_26715,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26693])).

tff(c_26694,plain,
    ( k1_relat_1('#skF_5') = k1_xboole_0
    | k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26686,c_26])).

tff(c_26722,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26715,c_26694])).

tff(c_28095,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28094,c_26722])).

tff(c_28144,plain,(
    ! [A_697,B_698,C_699] :
      ( k1_relset_1(A_697,B_698,C_699) = k1_relat_1(C_699)
      | ~ m1_subset_1(C_699,k1_zfmisc_1(k2_zfmisc_1(A_697,B_698))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28176,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_28144])).

tff(c_28632,plain,(
    ! [B_715,A_716,C_717] :
      ( k1_xboole_0 = B_715
      | k1_relset_1(A_716,B_715,C_717) = A_716
      | ~ v1_funct_2(C_717,A_716,B_715)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(k2_zfmisc_1(A_716,B_715))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28656,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_28632])).

tff(c_28676,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_28176,c_28656])).

tff(c_28677,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_28095,c_28676])).

tff(c_28686,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28677,c_26715])).

tff(c_28173,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_26478,c_28144])).

tff(c_28837,plain,(
    ! [B_725,C_726,A_727] :
      ( k1_xboole_0 = B_725
      | v1_funct_2(C_726,A_727,B_725)
      | k1_relset_1(A_727,B_725,C_726) != A_727
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(A_727,B_725))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28846,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_26478,c_28837])).

tff(c_28867,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28173,c_28846])).

tff(c_28868,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26477,c_28686,c_28867])).

tff(c_28880,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_28868])).

tff(c_28883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26686,c_88,c_82,c_28094,c_28880])).

tff(c_28884,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26693])).

tff(c_28885,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26693])).

tff(c_30802,plain,(
    ! [A_790] :
      ( m1_subset_1(A_790,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_790),k2_relat_1(A_790))))
      | ~ v1_funct_1(A_790)
      | ~ v1_relat_1(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30837,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_5'))))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28885,c_30802])).

tff(c_30869,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26686,c_88,c_16,c_28884,c_30837])).

tff(c_30885,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30869,c_20])).

tff(c_30893,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30885])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30921,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30893,c_8])).

tff(c_131,plain,(
    ! [A_53] :
      ( v1_xboole_0(k2_relat_1(A_53))
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_143,plain,(
    ! [A_56] :
      ( k2_relat_1(A_56) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_151,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_30969,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30921,c_30921,c_151])).

tff(c_31092,plain,(
    ! [A_797,B_798,C_799] :
      ( k2_relset_1(A_797,B_798,C_799) = k2_relat_1(C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_31107,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_31092])).

tff(c_31113,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30969,c_80,c_31107])).

tff(c_31122,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31113,c_30893])).

tff(c_31134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26551,c_31122])).

tff(c_31136,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26541])).

tff(c_31190,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31136,c_8])).

tff(c_31357,plain,(
    ! [B_812,A_813] :
      ( k1_xboole_0 = B_812
      | k1_xboole_0 = A_813
      | k2_zfmisc_1(A_813,B_812) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31370,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_31190,c_31357])).

tff(c_31376,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_31370])).

tff(c_31407,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31376,c_6])).

tff(c_31404,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31376,c_31376,c_16])).

tff(c_31541,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31404,c_510])).

tff(c_31545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31407,c_31541])).

tff(c_31546,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_31370])).

tff(c_31579,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31546,c_6])).

tff(c_31581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_31579])).

tff(c_31583,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_31582,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_31600,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_31582,c_8])).

tff(c_53567,plain,(
    ! [A_1428] :
      ( A_1428 = '#skF_5'
      | ~ v1_xboole_0(A_1428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_8])).

tff(c_53580,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_31583,c_53567])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k1_xboole_0 = B_11
      | k1_xboole_0 = A_10
      | k2_zfmisc_1(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54072,plain,(
    ! [B_1455,A_1456] :
      ( B_1455 = '#skF_5'
      | A_1456 = '#skF_5'
      | k2_zfmisc_1(A_1456,B_1455) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_31600,c_14])).

tff(c_54082,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_53580,c_54072])).

tff(c_54108,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54082])).

tff(c_53585,plain,(
    ! [A_1429] : k2_zfmisc_1(A_1429,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_16])).

tff(c_70,plain,(
    ! [A_35,B_36] : m1_subset_1('#skF_2'(A_35,B_36),k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_53727,plain,(
    ! [A_1436] : m1_subset_1('#skF_2'(A_1436,'#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53585,c_70])).

tff(c_53730,plain,(
    ! [A_1436] :
      ( v1_xboole_0('#skF_2'(A_1436,'#skF_5'))
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_53727,c_20])).

tff(c_53734,plain,(
    ! [A_1437] : v1_xboole_0('#skF_2'(A_1437,'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31582,c_53730])).

tff(c_31610,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_8])).

tff(c_53756,plain,(
    ! [A_1438] : '#skF_2'(A_1438,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53734,c_31610])).

tff(c_60,plain,(
    ! [A_35,B_36] : v1_funct_2('#skF_2'(A_35,B_36),A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_53764,plain,(
    ! [A_1438] : v1_funct_2('#skF_5',A_1438,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53756,c_60])).

tff(c_54417,plain,(
    ! [A_1438] : v1_funct_2('#skF_3',A_1438,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54108,c_54108,c_53764])).

tff(c_31653,plain,(
    ! [A_825] :
      ( A_825 = '#skF_5'
      | ~ v1_xboole_0(A_825) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_8])).

tff(c_31666,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_31583,c_31653])).

tff(c_31816,plain,(
    ! [B_834,A_835] :
      ( B_834 = '#skF_5'
      | A_835 = '#skF_5'
      | k2_zfmisc_1(A_835,B_834) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_31600,c_14])).

tff(c_31826,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_31666,c_31816])).

tff(c_31849,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_31826])).

tff(c_135,plain,(
    ! [A_53] :
      ( k2_relat_1(A_53) = k1_xboole_0
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_31598,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31582,c_135])).

tff(c_31618,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31598])).

tff(c_31865,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31849,c_31618])).

tff(c_18,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_31671,plain,(
    ! [B_826] : k2_zfmisc_1('#skF_5',B_826) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_18])).

tff(c_31808,plain,(
    ! [B_833] : m1_subset_1('#skF_2'('#skF_5',B_833),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31671,c_70])).

tff(c_31811,plain,(
    ! [B_833] :
      ( v1_xboole_0('#skF_2'('#skF_5',B_833))
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_31808,c_20])).

tff(c_31831,plain,(
    ! [B_836] : v1_xboole_0('#skF_2'('#skF_5',B_836)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31582,c_31811])).

tff(c_31846,plain,(
    ! [B_836] : '#skF_2'('#skF_5',B_836) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_31831,c_31610])).

tff(c_32026,plain,(
    ! [B_836] : '#skF_2'('#skF_3',B_836) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31849,c_31846])).

tff(c_33271,plain,(
    ! [A_899,B_900,C_901] :
      ( k2_relset_1(A_899,B_900,C_901) = k2_relat_1(C_901)
      | ~ m1_subset_1(C_901,k1_zfmisc_1(k2_zfmisc_1(A_899,B_900))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_37567,plain,(
    ! [A_1033,B_1034] : k2_relset_1(A_1033,B_1034,'#skF_2'(A_1033,B_1034)) = k2_relat_1('#skF_2'(A_1033,B_1034)) ),
    inference(resolution,[status(thm)],[c_70,c_33271])).

tff(c_37594,plain,(
    ! [B_836] : k2_relat_1('#skF_2'('#skF_3',B_836)) = k2_relset_1('#skF_3',B_836,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32026,c_37567])).

tff(c_37600,plain,(
    ! [B_1035] : k2_relset_1('#skF_3',B_1035,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31865,c_32026,c_37594])).

tff(c_31869,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_80])).

tff(c_37604,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_37600,c_31869])).

tff(c_226,plain,(
    ! [A_66] : m1_subset_1(k6_partfun1(A_66),k1_zfmisc_1(k2_zfmisc_1(A_66,A_66))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_230,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_226])).

tff(c_467,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_230,c_464])).

tff(c_476,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_467])).

tff(c_495,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_476,c_8])).

tff(c_31601,plain,(
    k6_partfun1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_495])).

tff(c_31864,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31849,c_31601])).

tff(c_58,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_31896,plain,(
    ! [C_837,A_838,B_839] :
      ( v1_relat_1(C_837)
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_31905,plain,(
    ! [A_34] : v1_relat_1(k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_58,c_31896])).

tff(c_31909,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31864,c_31905])).

tff(c_37690,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_31909])).

tff(c_31872,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_88])).

tff(c_37697,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_31872])).

tff(c_31609,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_16])).

tff(c_31859,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31849,c_31609])).

tff(c_31646,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_31860,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31646])).

tff(c_32122,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31859,c_31860])).

tff(c_37678,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_37604,c_32122])).

tff(c_31871,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_82])).

tff(c_37696,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_31871])).

tff(c_31868,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_376])).

tff(c_37692,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_31868])).

tff(c_37686,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_37604,c_31859])).

tff(c_31680,plain,(
    m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31671,c_58])).

tff(c_31687,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31601,c_31680])).

tff(c_31858,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31849,c_31687])).

tff(c_32517,plain,(
    ! [A_878,B_879,C_880] :
      ( k1_relset_1(A_878,B_879,C_880) = k1_relat_1(C_880)
      | ~ m1_subset_1(C_880,k1_zfmisc_1(k2_zfmisc_1(A_878,B_879))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_33532,plain,(
    ! [A_912] : k1_relset_1(A_912,A_912,k6_partfun1(A_912)) = k1_relat_1(k6_partfun1(A_912)) ),
    inference(resolution,[status(thm)],[c_58,c_32517])).

tff(c_33556,plain,(
    k1_relat_1(k6_partfun1('#skF_3')) = k1_relset_1('#skF_3','#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31864,c_33532])).

tff(c_33559,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31864,c_33556])).

tff(c_31867,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31582])).

tff(c_31692,plain,(
    ! [A_827] : k2_zfmisc_1(A_827,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_16])).

tff(c_31700,plain,(
    ! [A_827] : m1_subset_1('#skF_2'(A_827,'#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31692,c_70])).

tff(c_32087,plain,(
    ! [A_855] : m1_subset_1('#skF_2'(A_855,'#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31849,c_31700])).

tff(c_32092,plain,(
    ! [A_855] :
      ( v1_xboole_0('#skF_2'(A_855,'#skF_3'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32087,c_20])).

tff(c_32103,plain,(
    ! [A_856] : v1_xboole_0('#skF_2'(A_856,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31867,c_32092])).

tff(c_31862,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31610])).

tff(c_32127,plain,(
    ! [A_857] : '#skF_2'(A_857,'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32103,c_31862])).

tff(c_32138,plain,(
    ! [A_857] : v1_funct_2('#skF_3',A_857,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32127,c_60])).

tff(c_31866,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31849,c_31600])).

tff(c_52,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_89,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_34094,plain,(
    ! [B_933,C_934] :
      ( k1_relset_1('#skF_3',B_933,C_934) = '#skF_3'
      | ~ v1_funct_2(C_934,'#skF_3',B_933)
      | ~ m1_subset_1(C_934,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31866,c_31866,c_31866,c_31866,c_89])).

tff(c_34097,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32138,c_34094])).

tff(c_34105,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31858,c_33559,c_34097])).

tff(c_37645,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37604,c_37604,c_34105])).

tff(c_32795,plain,(
    ! [A_889] :
      ( m1_subset_1(A_889,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_889),k2_relat_1(A_889))))
      | ~ v1_funct_1(A_889)
      | ~ v1_relat_1(A_889) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38965,plain,(
    ! [A_1073] :
      ( m1_subset_1(k2_funct_1(A_1073),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1073)),k1_relat_1(A_1073))))
      | ~ v1_funct_1(k2_funct_1(A_1073))
      | ~ v1_relat_1(k2_funct_1(A_1073))
      | ~ v2_funct_1(A_1073)
      | ~ v1_funct_1(A_1073)
      | ~ v1_relat_1(A_1073) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_32795])).

tff(c_38985,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37645,c_38965])).

tff(c_39000,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37690,c_37697,c_37696,c_37692,c_37686,c_38985])).

tff(c_39001,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_37678,c_39000])).

tff(c_39004,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_39001])).

tff(c_39008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37690,c_37697,c_39004])).

tff(c_39009,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31826])).

tff(c_39025,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_39009,c_31601])).

tff(c_39058,plain,(
    ! [C_1074,A_1075,B_1076] :
      ( v1_relat_1(C_1074)
      | ~ m1_subset_1(C_1074,k1_zfmisc_1(k2_zfmisc_1(A_1075,B_1076))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_39067,plain,(
    ! [A_34] : v1_relat_1(k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_58,c_39058])).

tff(c_39071,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39025,c_39067])).

tff(c_39033,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_88])).

tff(c_31611,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_5',B_11) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_18])).

tff(c_39022,plain,(
    ! [B_11] : k2_zfmisc_1('#skF_4',B_11) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_39009,c_31611])).

tff(c_39021,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_31646])).

tff(c_39322,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39022,c_39021])).

tff(c_39032,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_82])).

tff(c_39029,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_376])).

tff(c_39020,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_39009,c_31609])).

tff(c_39019,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_39009,c_31687])).

tff(c_39188,plain,(
    ! [B_836] : '#skF_2'('#skF_4',B_836) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_39009,c_31846])).

tff(c_39027,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39009,c_31600])).

tff(c_41034,plain,(
    ! [B_1160,C_1161] :
      ( k1_relset_1('#skF_4',B_1160,C_1161) = '#skF_4'
      | ~ v1_funct_2(C_1161,'#skF_4',B_1160)
      | ~ m1_subset_1(C_1161,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39027,c_39027,c_39027,c_39027,c_89])).

tff(c_41042,plain,(
    ! [B_36] :
      ( k1_relset_1('#skF_4',B_36,'#skF_2'('#skF_4',B_36)) = '#skF_4'
      | ~ m1_subset_1('#skF_2'('#skF_4',B_36),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_41034])).

tff(c_41051,plain,(
    ! [B_36] : k1_relset_1('#skF_4',B_36,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39019,c_39188,c_39188,c_41042])).

tff(c_40507,plain,(
    ! [A_1139,B_1140,C_1141] :
      ( k1_relset_1(A_1139,B_1140,C_1141) = k1_relat_1(C_1141)
      | ~ m1_subset_1(C_1141,k1_zfmisc_1(k2_zfmisc_1(A_1139,B_1140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_41549,plain,(
    ! [A_1183] : k1_relset_1(A_1183,A_1183,k6_partfun1(A_1183)) = k1_relat_1(k6_partfun1(A_1183)) ),
    inference(resolution,[status(thm)],[c_58,c_40507])).

tff(c_41576,plain,(
    k1_relat_1(k6_partfun1('#skF_4')) = k1_relset_1('#skF_4','#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39025,c_41549])).

tff(c_41579,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41051,c_39025,c_41576])).

tff(c_39994,plain,(
    ! [A_1128] :
      ( m1_subset_1(A_1128,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1128),k2_relat_1(A_1128))))
      | ~ v1_funct_1(A_1128)
      | ~ v1_relat_1(A_1128) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_53442,plain,(
    ! [A_1427] :
      ( m1_subset_1(k2_funct_1(A_1427),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1427)),k1_relat_1(A_1427))))
      | ~ v1_funct_1(k2_funct_1(A_1427))
      | ~ v1_relat_1(k2_funct_1(A_1427))
      | ~ v2_funct_1(A_1427)
      | ~ v1_funct_1(A_1427)
      | ~ v1_relat_1(A_1427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_39994])).

tff(c_53507,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_41579,c_53442])).

tff(c_53550,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39071,c_39033,c_39032,c_39029,c_39020,c_53507])).

tff(c_53551,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_39322,c_53550])).

tff(c_53554,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_53551])).

tff(c_53558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39071,c_39033,c_53554])).

tff(c_53560,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_53651,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_53560,c_20])).

tff(c_53819,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_53651])).

tff(c_53823,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_53819])).

tff(c_53827,plain,(
    ! [B_1445,A_1446] :
      ( B_1445 = '#skF_5'
      | A_1446 = '#skF_5'
      | k2_zfmisc_1(A_1446,B_1445) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31600,c_31600,c_14])).

tff(c_53837,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_53580,c_53827])).

tff(c_53842,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_53837])).

tff(c_53865,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53842,c_31582])).

tff(c_53858,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53842,c_53842,c_31609])).

tff(c_53976,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53858,c_53819])).

tff(c_53979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53865,c_53976])).

tff(c_53980,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_53837])).

tff(c_54005,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53980,c_31582])).

tff(c_54012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53823,c_54005])).

tff(c_54013,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_53651])).

tff(c_54029,plain,(
    k2_funct_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_54013,c_31610])).

tff(c_53559,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_54035,plain,(
    ~ v1_funct_2('#skF_5','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54029,c_53559])).

tff(c_54109,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54108,c_54035])).

tff(c_54420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54417,c_54109])).

tff(c_54421,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54082])).

tff(c_54444,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54421,c_31582])).

tff(c_167,plain,(
    ! [A_60,B_61] :
      ( v1_xboole_0(k2_zfmisc_1(A_60,B_61))
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_184,plain,(
    ! [A_60,B_61] :
      ( k2_zfmisc_1(A_60,B_61) = k1_xboole_0
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_31597,plain,(
    ! [B_61] : k2_zfmisc_1('#skF_5',B_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31582,c_184])).

tff(c_53605,plain,(
    ! [B_1430] : k2_zfmisc_1('#skF_5',B_1430) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31600,c_31597])).

tff(c_53613,plain,(
    ! [B_1430] : m1_subset_1('#skF_2'('#skF_5',B_1430),k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53605,c_70])).

tff(c_54784,plain,(
    ! [B_1489] : m1_subset_1('#skF_2'('#skF_4',B_1489),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54421,c_54421,c_53613])).

tff(c_54789,plain,(
    ! [B_1489] :
      ( v1_xboole_0('#skF_2'('#skF_4',B_1489))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54784,c_20])).

tff(c_54800,plain,(
    ! [B_1490] : v1_xboole_0('#skF_2'('#skF_4',B_1490)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54444,c_54789])).

tff(c_54439,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54421,c_31610])).

tff(c_54826,plain,(
    ! [B_1491] : '#skF_2'('#skF_4',B_1491) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54800,c_54439])).

tff(c_54837,plain,(
    ! [B_1491] : v1_funct_2('#skF_4','#skF_4',B_1491) ),
    inference(superposition,[status(thm),theory(equality)],[c_54826,c_60])).

tff(c_54423,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54421,c_54035])).

tff(c_54879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54837,c_54423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:18:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.74/6.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.74/6.44  
% 14.74/6.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.74/6.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 14.74/6.44  
% 14.74/6.44  %Foreground sorts:
% 14.74/6.44  
% 14.74/6.44  
% 14.74/6.44  %Background operators:
% 14.74/6.44  
% 14.74/6.44  
% 14.74/6.44  %Foreground operators:
% 14.74/6.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.74/6.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.74/6.44  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.74/6.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.74/6.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.74/6.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.74/6.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.74/6.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.74/6.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.74/6.44  tff('#skF_5', type, '#skF_5': $i).
% 14.74/6.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.74/6.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.74/6.44  tff('#skF_3', type, '#skF_3': $i).
% 14.74/6.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.74/6.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.74/6.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.74/6.45  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.74/6.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.74/6.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.74/6.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.74/6.45  tff('#skF_4', type, '#skF_4': $i).
% 14.74/6.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.74/6.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.74/6.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.74/6.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.74/6.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.74/6.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.74/6.45  
% 15.12/6.48  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 15.12/6.48  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 15.12/6.48  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 15.12/6.48  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.12/6.48  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.12/6.48  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.12/6.48  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 15.12/6.48  tff(f_78, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 15.12/6.48  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.12/6.48  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.12/6.48  tff(f_153, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 15.12/6.48  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.12/6.48  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.12/6.48  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 15.12/6.48  tff(f_72, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 15.12/6.48  tff(f_143, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 15.12/6.48  tff(f_130, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 15.12/6.48  tff(c_12, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.12/6.48  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.12/6.48  tff(c_464, plain, (![B_90, A_91]: (v1_xboole_0(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.12/6.48  tff(c_478, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_464])).
% 15.12/6.48  tff(c_510, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_478])).
% 15.12/6.48  tff(c_514, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_510])).
% 15.12/6.48  tff(c_88, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.12/6.48  tff(c_30, plain, (![A_20]: (v1_funct_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.12/6.48  tff(c_78, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.12/6.48  tff(c_237, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_78])).
% 15.12/6.48  tff(c_240, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_237])).
% 15.12/6.48  tff(c_243, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_240])).
% 15.12/6.48  tff(c_352, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.12/6.48  tff(c_363, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_352])).
% 15.12/6.48  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_363])).
% 15.12/6.48  tff(c_375, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_78])).
% 15.12/6.48  tff(c_539, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_375])).
% 15.12/6.48  tff(c_712, plain, (![C_107, A_108, B_109]: (v1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.12/6.48  tff(c_731, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_712])).
% 15.12/6.48  tff(c_82, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.12/6.48  tff(c_80, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.12/6.48  tff(c_1121, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.12/6.48  tff(c_1133, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_1121])).
% 15.12/6.48  tff(c_1143, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1133])).
% 15.12/6.48  tff(c_36, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.12/6.48  tff(c_32, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.12/6.48  tff(c_376, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_78])).
% 15.12/6.48  tff(c_28, plain, (![A_19]: (k2_relat_1(A_19)=k1_xboole_0 | k1_relat_1(A_19)!=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.12/6.48  tff(c_738, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_731, c_28])).
% 15.12/6.48  tff(c_758, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_738])).
% 15.12/6.48  tff(c_26, plain, (![A_19]: (k1_relat_1(A_19)=k1_xboole_0 | k2_relat_1(A_19)!=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.12/6.48  tff(c_739, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_731, c_26])).
% 15.12/6.48  tff(c_781, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_758, c_739])).
% 15.12/6.48  tff(c_1144, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_781])).
% 15.12/6.48  tff(c_86, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 15.12/6.48  tff(c_1250, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.12/6.48  tff(c_1279, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_1250])).
% 15.12/6.48  tff(c_2440, plain, (![B_179, A_180, C_181]: (k1_xboole_0=B_179 | k1_relset_1(A_180, B_179, C_181)=A_180 | ~v1_funct_2(C_181, A_180, B_179) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_180, B_179))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.12/6.48  tff(c_2461, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_2440])).
% 15.12/6.48  tff(c_2480, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1279, c_2461])).
% 15.12/6.48  tff(c_2481, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1144, c_2480])).
% 15.12/6.48  tff(c_871, plain, (![A_120]: (k2_relat_1(k2_funct_1(A_120))=k1_relat_1(A_120) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.12/6.48  tff(c_74, plain, (![A_38]: (v1_funct_2(A_38, k1_relat_1(A_38), k2_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.12/6.48  tff(c_21427, plain, (![A_550]: (v1_funct_2(k2_funct_1(A_550), k1_relat_1(k2_funct_1(A_550)), k1_relat_1(A_550)) | ~v1_funct_1(k2_funct_1(A_550)) | ~v1_relat_1(k2_funct_1(A_550)) | ~v2_funct_1(A_550) | ~v1_funct_1(A_550) | ~v1_relat_1(A_550))), inference(superposition, [status(thm), theory('equality')], [c_871, c_74])).
% 15.12/6.48  tff(c_21481, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2481, c_21427])).
% 15.12/6.48  tff(c_21526, plain, (v1_funct_2(k2_funct_1('#skF_5'), k1_relat_1(k2_funct_1('#skF_5')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_88, c_82, c_376, c_21481])).
% 15.12/6.48  tff(c_22119, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_21526])).
% 15.12/6.48  tff(c_22122, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_22119])).
% 15.12/6.48  tff(c_22126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_731, c_88, c_22122])).
% 15.12/6.48  tff(c_22128, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_21526])).
% 15.12/6.48  tff(c_34, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.12/6.48  tff(c_1173, plain, (![A_133]: (m1_subset_1(A_133, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_133), k2_relat_1(A_133)))) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.12/6.48  tff(c_25506, plain, (![A_589]: (m1_subset_1(k2_funct_1(A_589), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_589)), k1_relat_1(A_589)))) | ~v1_funct_1(k2_funct_1(A_589)) | ~v1_relat_1(k2_funct_1(A_589)) | ~v2_funct_1(A_589) | ~v1_funct_1(A_589) | ~v1_relat_1(A_589))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1173])).
% 15.12/6.48  tff(c_25589, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2481, c_25506])).
% 15.12/6.48  tff(c_25647, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_5')), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_88, c_82, c_22128, c_376, c_25589])).
% 15.12/6.48  tff(c_25672, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_5'), '#skF_3'))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_25647])).
% 15.12/6.48  tff(c_25687, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_88, c_82, c_1143, c_25672])).
% 15.12/6.48  tff(c_25689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_539, c_25687])).
% 15.12/6.48  tff(c_25690, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_738])).
% 15.12/6.48  tff(c_26281, plain, (![A_612, B_613, C_614]: (k2_relset_1(A_612, B_613, C_614)=k2_relat_1(C_614) | ~m1_subset_1(C_614, k1_zfmisc_1(k2_zfmisc_1(A_612, B_613))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.12/6.48  tff(c_26296, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_26281])).
% 15.12/6.48  tff(c_26306, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25690, c_80, c_26296])).
% 15.12/6.48  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.12/6.48  tff(c_26344, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26306, c_6])).
% 15.12/6.48  tff(c_16, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.12/6.48  tff(c_26341, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26306, c_26306, c_16])).
% 15.12/6.48  tff(c_26472, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26341, c_510])).
% 15.12/6.48  tff(c_26476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26344, c_26472])).
% 15.12/6.48  tff(c_26478, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_375])).
% 15.12/6.48  tff(c_20, plain, (![B_14, A_12]: (v1_xboole_0(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.12/6.48  tff(c_26541, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26478, c_20])).
% 15.12/6.48  tff(c_26547, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_26541])).
% 15.12/6.48  tff(c_26551, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_12, c_26547])).
% 15.12/6.48  tff(c_26663, plain, (![C_636, A_637, B_638]: (v1_relat_1(C_636) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(A_637, B_638))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.12/6.48  tff(c_26686, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_26663])).
% 15.12/6.48  tff(c_28061, plain, (![A_694, B_695, C_696]: (k2_relset_1(A_694, B_695, C_696)=k2_relat_1(C_696) | ~m1_subset_1(C_696, k1_zfmisc_1(k2_zfmisc_1(A_694, B_695))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.12/6.48  tff(c_28082, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_28061])).
% 15.12/6.48  tff(c_28094, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_28082])).
% 15.12/6.48  tff(c_26477, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_375])).
% 15.12/6.48  tff(c_26693, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_26686, c_28])).
% 15.12/6.48  tff(c_26715, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26693])).
% 15.12/6.48  tff(c_26694, plain, (k1_relat_1('#skF_5')=k1_xboole_0 | k2_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_26686, c_26])).
% 15.12/6.48  tff(c_26722, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26715, c_26694])).
% 15.12/6.48  tff(c_28095, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28094, c_26722])).
% 15.12/6.48  tff(c_28144, plain, (![A_697, B_698, C_699]: (k1_relset_1(A_697, B_698, C_699)=k1_relat_1(C_699) | ~m1_subset_1(C_699, k1_zfmisc_1(k2_zfmisc_1(A_697, B_698))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.12/6.48  tff(c_28176, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_28144])).
% 15.12/6.48  tff(c_28632, plain, (![B_715, A_716, C_717]: (k1_xboole_0=B_715 | k1_relset_1(A_716, B_715, C_717)=A_716 | ~v1_funct_2(C_717, A_716, B_715) | ~m1_subset_1(C_717, k1_zfmisc_1(k2_zfmisc_1(A_716, B_715))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.12/6.48  tff(c_28656, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_28632])).
% 15.12/6.48  tff(c_28676, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_28176, c_28656])).
% 15.12/6.48  tff(c_28677, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_28095, c_28676])).
% 15.12/6.48  tff(c_28686, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28677, c_26715])).
% 15.12/6.48  tff(c_28173, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_26478, c_28144])).
% 15.12/6.48  tff(c_28837, plain, (![B_725, C_726, A_727]: (k1_xboole_0=B_725 | v1_funct_2(C_726, A_727, B_725) | k1_relset_1(A_727, B_725, C_726)!=A_727 | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(A_727, B_725))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.12/6.48  tff(c_28846, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_26478, c_28837])).
% 15.12/6.48  tff(c_28867, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28173, c_28846])).
% 15.12/6.48  tff(c_28868, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26477, c_28686, c_28867])).
% 15.12/6.48  tff(c_28880, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_28868])).
% 15.12/6.48  tff(c_28883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26686, c_88, c_82, c_28094, c_28880])).
% 15.12/6.48  tff(c_28884, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26693])).
% 15.12/6.48  tff(c_28885, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26693])).
% 15.12/6.48  tff(c_30802, plain, (![A_790]: (m1_subset_1(A_790, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_790), k2_relat_1(A_790)))) | ~v1_funct_1(A_790) | ~v1_relat_1(A_790))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.12/6.48  tff(c_30837, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_5')))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28885, c_30802])).
% 15.12/6.48  tff(c_30869, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26686, c_88, c_16, c_28884, c_30837])).
% 15.12/6.48  tff(c_30885, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_30869, c_20])).
% 15.12/6.48  tff(c_30893, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30885])).
% 15.12/6.48  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.12/6.48  tff(c_30921, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_30893, c_8])).
% 15.12/6.48  tff(c_131, plain, (![A_53]: (v1_xboole_0(k2_relat_1(A_53)) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.12/6.48  tff(c_143, plain, (![A_56]: (k2_relat_1(A_56)=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_131, c_8])).
% 15.12/6.48  tff(c_151, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_143])).
% 15.12/6.48  tff(c_30969, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30921, c_30921, c_151])).
% 15.12/6.48  tff(c_31092, plain, (![A_797, B_798, C_799]: (k2_relset_1(A_797, B_798, C_799)=k2_relat_1(C_799) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.12/6.48  tff(c_31107, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_31092])).
% 15.12/6.48  tff(c_31113, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30969, c_80, c_31107])).
% 15.12/6.48  tff(c_31122, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31113, c_30893])).
% 15.12/6.48  tff(c_31134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26551, c_31122])).
% 15.12/6.48  tff(c_31136, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_26541])).
% 15.12/6.48  tff(c_31190, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_31136, c_8])).
% 15.12/6.48  tff(c_31357, plain, (![B_812, A_813]: (k1_xboole_0=B_812 | k1_xboole_0=A_813 | k2_zfmisc_1(A_813, B_812)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.12/6.48  tff(c_31370, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_31190, c_31357])).
% 15.12/6.48  tff(c_31376, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_31370])).
% 15.12/6.48  tff(c_31407, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31376, c_6])).
% 15.12/6.48  tff(c_31404, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31376, c_31376, c_16])).
% 15.12/6.48  tff(c_31541, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31404, c_510])).
% 15.12/6.48  tff(c_31545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31407, c_31541])).
% 15.12/6.48  tff(c_31546, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_31370])).
% 15.12/6.48  tff(c_31579, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31546, c_6])).
% 15.12/6.48  tff(c_31581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_31579])).
% 15.12/6.48  tff(c_31583, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_478])).
% 15.12/6.48  tff(c_31582, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_478])).
% 15.12/6.48  tff(c_31600, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_31582, c_8])).
% 15.12/6.48  tff(c_53567, plain, (![A_1428]: (A_1428='#skF_5' | ~v1_xboole_0(A_1428))), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_8])).
% 15.12/6.48  tff(c_53580, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_31583, c_53567])).
% 15.12/6.48  tff(c_14, plain, (![B_11, A_10]: (k1_xboole_0=B_11 | k1_xboole_0=A_10 | k2_zfmisc_1(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.12/6.48  tff(c_54072, plain, (![B_1455, A_1456]: (B_1455='#skF_5' | A_1456='#skF_5' | k2_zfmisc_1(A_1456, B_1455)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_31600, c_14])).
% 15.12/6.48  tff(c_54082, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_53580, c_54072])).
% 15.12/6.48  tff(c_54108, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_54082])).
% 15.12/6.48  tff(c_53585, plain, (![A_1429]: (k2_zfmisc_1(A_1429, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_16])).
% 15.12/6.48  tff(c_70, plain, (![A_35, B_36]: (m1_subset_1('#skF_2'(A_35, B_36), k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.12/6.48  tff(c_53727, plain, (![A_1436]: (m1_subset_1('#skF_2'(A_1436, '#skF_5'), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_53585, c_70])).
% 15.12/6.48  tff(c_53730, plain, (![A_1436]: (v1_xboole_0('#skF_2'(A_1436, '#skF_5')) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_53727, c_20])).
% 15.12/6.48  tff(c_53734, plain, (![A_1437]: (v1_xboole_0('#skF_2'(A_1437, '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_31582, c_53730])).
% 15.12/6.48  tff(c_31610, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_8])).
% 15.12/6.48  tff(c_53756, plain, (![A_1438]: ('#skF_2'(A_1438, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_53734, c_31610])).
% 15.12/6.48  tff(c_60, plain, (![A_35, B_36]: (v1_funct_2('#skF_2'(A_35, B_36), A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_143])).
% 15.12/6.48  tff(c_53764, plain, (![A_1438]: (v1_funct_2('#skF_5', A_1438, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_53756, c_60])).
% 15.12/6.48  tff(c_54417, plain, (![A_1438]: (v1_funct_2('#skF_3', A_1438, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54108, c_54108, c_53764])).
% 15.12/6.48  tff(c_31653, plain, (![A_825]: (A_825='#skF_5' | ~v1_xboole_0(A_825))), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_8])).
% 15.12/6.48  tff(c_31666, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_31583, c_31653])).
% 15.12/6.48  tff(c_31816, plain, (![B_834, A_835]: (B_834='#skF_5' | A_835='#skF_5' | k2_zfmisc_1(A_835, B_834)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_31600, c_14])).
% 15.12/6.48  tff(c_31826, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_31666, c_31816])).
% 15.12/6.48  tff(c_31849, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_31826])).
% 15.12/6.48  tff(c_135, plain, (![A_53]: (k2_relat_1(A_53)=k1_xboole_0 | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_131, c_8])).
% 15.12/6.48  tff(c_31598, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_31582, c_135])).
% 15.12/6.48  tff(c_31618, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31598])).
% 15.12/6.48  tff(c_31865, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31849, c_31618])).
% 15.12/6.48  tff(c_18, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.12/6.48  tff(c_31671, plain, (![B_826]: (k2_zfmisc_1('#skF_5', B_826)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_18])).
% 15.12/6.48  tff(c_31808, plain, (![B_833]: (m1_subset_1('#skF_2'('#skF_5', B_833), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_31671, c_70])).
% 15.12/6.48  tff(c_31811, plain, (![B_833]: (v1_xboole_0('#skF_2'('#skF_5', B_833)) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_31808, c_20])).
% 15.12/6.48  tff(c_31831, plain, (![B_836]: (v1_xboole_0('#skF_2'('#skF_5', B_836)))), inference(demodulation, [status(thm), theory('equality')], [c_31582, c_31811])).
% 15.12/6.48  tff(c_31846, plain, (![B_836]: ('#skF_2'('#skF_5', B_836)='#skF_5')), inference(resolution, [status(thm)], [c_31831, c_31610])).
% 15.12/6.48  tff(c_32026, plain, (![B_836]: ('#skF_2'('#skF_3', B_836)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31849, c_31846])).
% 15.12/6.48  tff(c_33271, plain, (![A_899, B_900, C_901]: (k2_relset_1(A_899, B_900, C_901)=k2_relat_1(C_901) | ~m1_subset_1(C_901, k1_zfmisc_1(k2_zfmisc_1(A_899, B_900))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.12/6.48  tff(c_37567, plain, (![A_1033, B_1034]: (k2_relset_1(A_1033, B_1034, '#skF_2'(A_1033, B_1034))=k2_relat_1('#skF_2'(A_1033, B_1034)))), inference(resolution, [status(thm)], [c_70, c_33271])).
% 15.12/6.48  tff(c_37594, plain, (![B_836]: (k2_relat_1('#skF_2'('#skF_3', B_836))=k2_relset_1('#skF_3', B_836, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32026, c_37567])).
% 15.12/6.48  tff(c_37600, plain, (![B_1035]: (k2_relset_1('#skF_3', B_1035, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31865, c_32026, c_37594])).
% 15.12/6.48  tff(c_31869, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_80])).
% 15.12/6.48  tff(c_37604, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_37600, c_31869])).
% 15.12/6.48  tff(c_226, plain, (![A_66]: (m1_subset_1(k6_partfun1(A_66), k1_zfmisc_1(k2_zfmisc_1(A_66, A_66))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.12/6.48  tff(c_230, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_226])).
% 15.12/6.48  tff(c_467, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_230, c_464])).
% 15.12/6.48  tff(c_476, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_467])).
% 15.12/6.48  tff(c_495, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_476, c_8])).
% 15.12/6.48  tff(c_31601, plain, (k6_partfun1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_495])).
% 15.12/6.48  tff(c_31864, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31849, c_31601])).
% 15.12/6.48  tff(c_58, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.12/6.48  tff(c_31896, plain, (![C_837, A_838, B_839]: (v1_relat_1(C_837) | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.12/6.48  tff(c_31905, plain, (![A_34]: (v1_relat_1(k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_58, c_31896])).
% 15.12/6.48  tff(c_31909, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_31864, c_31905])).
% 15.12/6.48  tff(c_37690, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_31909])).
% 15.12/6.48  tff(c_31872, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_88])).
% 15.12/6.48  tff(c_37697, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_31872])).
% 15.12/6.48  tff(c_31609, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_16])).
% 15.12/6.48  tff(c_31859, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31849, c_31609])).
% 15.12/6.48  tff(c_31646, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_375])).
% 15.12/6.48  tff(c_31860, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31646])).
% 15.12/6.48  tff(c_32122, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31859, c_31860])).
% 15.12/6.48  tff(c_37678, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_37604, c_32122])).
% 15.12/6.48  tff(c_31871, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_82])).
% 15.12/6.48  tff(c_37696, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_31871])).
% 15.12/6.48  tff(c_31868, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_376])).
% 15.12/6.48  tff(c_37692, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_31868])).
% 15.12/6.48  tff(c_37686, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_37604, c_31859])).
% 15.12/6.48  tff(c_31680, plain, (m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_31671, c_58])).
% 15.12/6.48  tff(c_31687, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_31601, c_31680])).
% 15.12/6.48  tff(c_31858, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31849, c_31687])).
% 15.12/6.48  tff(c_32517, plain, (![A_878, B_879, C_880]: (k1_relset_1(A_878, B_879, C_880)=k1_relat_1(C_880) | ~m1_subset_1(C_880, k1_zfmisc_1(k2_zfmisc_1(A_878, B_879))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.12/6.48  tff(c_33532, plain, (![A_912]: (k1_relset_1(A_912, A_912, k6_partfun1(A_912))=k1_relat_1(k6_partfun1(A_912)))), inference(resolution, [status(thm)], [c_58, c_32517])).
% 15.12/6.48  tff(c_33556, plain, (k1_relat_1(k6_partfun1('#skF_3'))=k1_relset_1('#skF_3', '#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_31864, c_33532])).
% 15.12/6.48  tff(c_33559, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31864, c_33556])).
% 15.12/6.48  tff(c_31867, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31582])).
% 15.12/6.48  tff(c_31692, plain, (![A_827]: (k2_zfmisc_1(A_827, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_16])).
% 15.12/6.48  tff(c_31700, plain, (![A_827]: (m1_subset_1('#skF_2'(A_827, '#skF_5'), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_31692, c_70])).
% 15.12/6.48  tff(c_32087, plain, (![A_855]: (m1_subset_1('#skF_2'(A_855, '#skF_3'), k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31849, c_31700])).
% 15.12/6.48  tff(c_32092, plain, (![A_855]: (v1_xboole_0('#skF_2'(A_855, '#skF_3')) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_32087, c_20])).
% 15.12/6.48  tff(c_32103, plain, (![A_856]: (v1_xboole_0('#skF_2'(A_856, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31867, c_32092])).
% 15.12/6.48  tff(c_31862, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31610])).
% 15.12/6.48  tff(c_32127, plain, (![A_857]: ('#skF_2'(A_857, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_32103, c_31862])).
% 15.12/6.48  tff(c_32138, plain, (![A_857]: (v1_funct_2('#skF_3', A_857, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32127, c_60])).
% 15.12/6.48  tff(c_31866, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31849, c_31600])).
% 15.12/6.48  tff(c_52, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.12/6.48  tff(c_89, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 15.12/6.48  tff(c_34094, plain, (![B_933, C_934]: (k1_relset_1('#skF_3', B_933, C_934)='#skF_3' | ~v1_funct_2(C_934, '#skF_3', B_933) | ~m1_subset_1(C_934, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_31866, c_31866, c_31866, c_31866, c_89])).
% 15.12/6.48  tff(c_34097, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_32138, c_34094])).
% 15.12/6.48  tff(c_34105, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_31858, c_33559, c_34097])).
% 15.12/6.48  tff(c_37645, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37604, c_37604, c_34105])).
% 15.12/6.48  tff(c_32795, plain, (![A_889]: (m1_subset_1(A_889, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_889), k2_relat_1(A_889)))) | ~v1_funct_1(A_889) | ~v1_relat_1(A_889))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.12/6.48  tff(c_38965, plain, (![A_1073]: (m1_subset_1(k2_funct_1(A_1073), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1073)), k1_relat_1(A_1073)))) | ~v1_funct_1(k2_funct_1(A_1073)) | ~v1_relat_1(k2_funct_1(A_1073)) | ~v2_funct_1(A_1073) | ~v1_funct_1(A_1073) | ~v1_relat_1(A_1073))), inference(superposition, [status(thm), theory('equality')], [c_34, c_32795])).
% 15.12/6.48  tff(c_38985, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37645, c_38965])).
% 15.12/6.48  tff(c_39000, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_37690, c_37697, c_37696, c_37692, c_37686, c_38985])).
% 15.12/6.48  tff(c_39001, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_37678, c_39000])).
% 15.12/6.48  tff(c_39004, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_39001])).
% 15.12/6.48  tff(c_39008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37690, c_37697, c_39004])).
% 15.12/6.48  tff(c_39009, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_31826])).
% 15.12/6.48  tff(c_39025, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_39009, c_31601])).
% 15.12/6.48  tff(c_39058, plain, (![C_1074, A_1075, B_1076]: (v1_relat_1(C_1074) | ~m1_subset_1(C_1074, k1_zfmisc_1(k2_zfmisc_1(A_1075, B_1076))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.12/6.48  tff(c_39067, plain, (![A_34]: (v1_relat_1(k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_58, c_39058])).
% 15.12/6.48  tff(c_39071, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39025, c_39067])).
% 15.12/6.48  tff(c_39033, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_88])).
% 15.12/6.48  tff(c_31611, plain, (![B_11]: (k2_zfmisc_1('#skF_5', B_11)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_18])).
% 15.12/6.48  tff(c_39022, plain, (![B_11]: (k2_zfmisc_1('#skF_4', B_11)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_39009, c_31611])).
% 15.12/6.48  tff(c_39021, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_31646])).
% 15.12/6.48  tff(c_39322, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39022, c_39021])).
% 15.12/6.48  tff(c_39032, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_82])).
% 15.12/6.48  tff(c_39029, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_376])).
% 15.12/6.48  tff(c_39020, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_39009, c_31609])).
% 15.12/6.48  tff(c_39019, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_39009, c_31687])).
% 15.12/6.48  tff(c_39188, plain, (![B_836]: ('#skF_2'('#skF_4', B_836)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_39009, c_31846])).
% 15.12/6.48  tff(c_39027, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39009, c_31600])).
% 15.12/6.48  tff(c_41034, plain, (![B_1160, C_1161]: (k1_relset_1('#skF_4', B_1160, C_1161)='#skF_4' | ~v1_funct_2(C_1161, '#skF_4', B_1160) | ~m1_subset_1(C_1161, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_39027, c_39027, c_39027, c_39027, c_89])).
% 15.12/6.48  tff(c_41042, plain, (![B_36]: (k1_relset_1('#skF_4', B_36, '#skF_2'('#skF_4', B_36))='#skF_4' | ~m1_subset_1('#skF_2'('#skF_4', B_36), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_60, c_41034])).
% 15.12/6.48  tff(c_41051, plain, (![B_36]: (k1_relset_1('#skF_4', B_36, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_39019, c_39188, c_39188, c_41042])).
% 15.12/6.48  tff(c_40507, plain, (![A_1139, B_1140, C_1141]: (k1_relset_1(A_1139, B_1140, C_1141)=k1_relat_1(C_1141) | ~m1_subset_1(C_1141, k1_zfmisc_1(k2_zfmisc_1(A_1139, B_1140))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.12/6.48  tff(c_41549, plain, (![A_1183]: (k1_relset_1(A_1183, A_1183, k6_partfun1(A_1183))=k1_relat_1(k6_partfun1(A_1183)))), inference(resolution, [status(thm)], [c_58, c_40507])).
% 15.12/6.48  tff(c_41576, plain, (k1_relat_1(k6_partfun1('#skF_4'))=k1_relset_1('#skF_4', '#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39025, c_41549])).
% 15.12/6.48  tff(c_41579, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41051, c_39025, c_41576])).
% 15.12/6.48  tff(c_39994, plain, (![A_1128]: (m1_subset_1(A_1128, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_1128), k2_relat_1(A_1128)))) | ~v1_funct_1(A_1128) | ~v1_relat_1(A_1128))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.12/6.48  tff(c_53442, plain, (![A_1427]: (m1_subset_1(k2_funct_1(A_1427), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1427)), k1_relat_1(A_1427)))) | ~v1_funct_1(k2_funct_1(A_1427)) | ~v1_relat_1(k2_funct_1(A_1427)) | ~v2_funct_1(A_1427) | ~v1_funct_1(A_1427) | ~v1_relat_1(A_1427))), inference(superposition, [status(thm), theory('equality')], [c_34, c_39994])).
% 15.12/6.48  tff(c_53507, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_41579, c_53442])).
% 15.12/6.48  tff(c_53550, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39071, c_39033, c_39032, c_39029, c_39020, c_53507])).
% 15.12/6.48  tff(c_53551, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_39322, c_53550])).
% 15.12/6.48  tff(c_53554, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_53551])).
% 15.12/6.48  tff(c_53558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39071, c_39033, c_53554])).
% 15.12/6.48  tff(c_53560, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_375])).
% 15.12/6.48  tff(c_53651, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_53560, c_20])).
% 15.12/6.48  tff(c_53819, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_53651])).
% 15.12/6.48  tff(c_53823, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_12, c_53819])).
% 15.12/6.48  tff(c_53827, plain, (![B_1445, A_1446]: (B_1445='#skF_5' | A_1446='#skF_5' | k2_zfmisc_1(A_1446, B_1445)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31600, c_31600, c_14])).
% 15.12/6.48  tff(c_53837, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_53580, c_53827])).
% 15.12/6.48  tff(c_53842, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_53837])).
% 15.12/6.48  tff(c_53865, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53842, c_31582])).
% 15.12/6.48  tff(c_53858, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53842, c_53842, c_31609])).
% 15.12/6.48  tff(c_53976, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53858, c_53819])).
% 15.12/6.48  tff(c_53979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53865, c_53976])).
% 15.12/6.48  tff(c_53980, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_53837])).
% 15.12/6.48  tff(c_54005, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53980, c_31582])).
% 15.12/6.48  tff(c_54012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53823, c_54005])).
% 15.12/6.48  tff(c_54013, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_53651])).
% 15.12/6.48  tff(c_54029, plain, (k2_funct_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_54013, c_31610])).
% 15.12/6.48  tff(c_53559, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_375])).
% 15.12/6.48  tff(c_54035, plain, (~v1_funct_2('#skF_5', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54029, c_53559])).
% 15.12/6.48  tff(c_54109, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54108, c_54035])).
% 15.12/6.48  tff(c_54420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54417, c_54109])).
% 15.12/6.48  tff(c_54421, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_54082])).
% 15.12/6.48  tff(c_54444, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54421, c_31582])).
% 15.12/6.48  tff(c_167, plain, (![A_60, B_61]: (v1_xboole_0(k2_zfmisc_1(A_60, B_61)) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.12/6.48  tff(c_184, plain, (![A_60, B_61]: (k2_zfmisc_1(A_60, B_61)=k1_xboole_0 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_167, c_8])).
% 15.12/6.48  tff(c_31597, plain, (![B_61]: (k2_zfmisc_1('#skF_5', B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_31582, c_184])).
% 15.12/6.48  tff(c_53605, plain, (![B_1430]: (k2_zfmisc_1('#skF_5', B_1430)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31600, c_31597])).
% 15.12/6.48  tff(c_53613, plain, (![B_1430]: (m1_subset_1('#skF_2'('#skF_5', B_1430), k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_53605, c_70])).
% 15.12/6.48  tff(c_54784, plain, (![B_1489]: (m1_subset_1('#skF_2'('#skF_4', B_1489), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54421, c_54421, c_53613])).
% 15.12/6.48  tff(c_54789, plain, (![B_1489]: (v1_xboole_0('#skF_2'('#skF_4', B_1489)) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_54784, c_20])).
% 15.12/6.48  tff(c_54800, plain, (![B_1490]: (v1_xboole_0('#skF_2'('#skF_4', B_1490)))), inference(demodulation, [status(thm), theory('equality')], [c_54444, c_54789])).
% 15.12/6.48  tff(c_54439, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_54421, c_31610])).
% 15.12/6.48  tff(c_54826, plain, (![B_1491]: ('#skF_2'('#skF_4', B_1491)='#skF_4')), inference(resolution, [status(thm)], [c_54800, c_54439])).
% 15.12/6.48  tff(c_54837, plain, (![B_1491]: (v1_funct_2('#skF_4', '#skF_4', B_1491))), inference(superposition, [status(thm), theory('equality')], [c_54826, c_60])).
% 15.12/6.48  tff(c_54423, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54421, c_54035])).
% 15.12/6.48  tff(c_54879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54837, c_54423])).
% 15.12/6.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.12/6.48  
% 15.12/6.48  Inference rules
% 15.12/6.48  ----------------------
% 15.12/6.48  #Ref     : 0
% 15.12/6.48  #Sup     : 13631
% 15.12/6.48  #Fact    : 0
% 15.12/6.48  #Define  : 0
% 15.12/6.48  #Split   : 19
% 15.12/6.48  #Chain   : 0
% 15.12/6.48  #Close   : 0
% 15.12/6.48  
% 15.12/6.48  Ordering : KBO
% 15.12/6.48  
% 15.12/6.48  Simplification rules
% 15.12/6.48  ----------------------
% 15.12/6.48  #Subsume      : 1542
% 15.12/6.48  #Demod        : 16694
% 15.12/6.48  #Tautology    : 8600
% 15.12/6.48  #SimpNegUnit  : 30
% 15.12/6.48  #BackRed      : 490
% 15.12/6.48  
% 15.12/6.48  #Partial instantiations: 0
% 15.12/6.48  #Strategies tried      : 1
% 15.12/6.48  
% 15.12/6.48  Timing (in seconds)
% 15.12/6.48  ----------------------
% 15.12/6.49  Preprocessing        : 0.37
% 15.12/6.49  Parsing              : 0.20
% 15.12/6.49  CNF conversion       : 0.03
% 15.12/6.49  Main loop            : 5.27
% 15.12/6.49  Inferencing          : 1.24
% 15.12/6.49  Reduction            : 1.86
% 15.12/6.49  Demodulation         : 1.42
% 15.12/6.49  BG Simplification    : 0.15
% 15.12/6.49  Subsumption          : 1.68
% 15.12/6.49  Abstraction          : 0.22
% 15.12/6.49  MUC search           : 0.00
% 15.12/6.49  Cooper               : 0.00
% 15.12/6.49  Total                : 5.74
% 15.12/6.49  Index Insertion      : 0.00
% 15.12/6.49  Index Deletion       : 0.00
% 15.12/6.49  Index Matching       : 0.00
% 15.12/6.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
