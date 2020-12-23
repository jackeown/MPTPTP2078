%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:38 EST 2020

% Result     : Theorem 10.78s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  441 (6463 expanded)
%              Number of leaves         :   43 (1972 expanded)
%              Depth                    :   19
%              Number of atoms          :  798 (16908 expanded)
%              Number of equality atoms :  286 (6210 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_163,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_212,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14158,plain,(
    ! [A_988,A_989,B_990] :
      ( v1_relat_1(A_988)
      | ~ r1_tarski(A_988,k2_zfmisc_1(A_989,B_990)) ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_14181,plain,(
    ! [A_989,B_990] : v1_relat_1(k2_zfmisc_1(A_989,B_990)) ),
    inference(resolution,[status(thm)],[c_6,c_14158])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_34,plain,(
    ! [A_19] :
      ( v1_funct_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_169,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_172,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_169])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_172])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_189,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_196,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_189])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_196])).

tff(c_210,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_244,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_273,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_244])).

tff(c_229,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_212])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_814,plain,(
    ! [A_140,B_141,C_142] :
      ( k1_relset_1(A_140,B_141,C_142) = k1_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_833,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_814])).

tff(c_4484,plain,(
    ! [B_336,A_337,C_338] :
      ( k1_xboole_0 = B_336
      | k1_relset_1(A_337,B_336,C_338) = A_337
      | ~ v1_funct_2(C_338,A_337,B_336)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_337,B_336))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4497,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_4484])).

tff(c_4512,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_833,c_4497])).

tff(c_4516,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4512])).

tff(c_36,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1025,plain,(
    ! [A_164,B_165,C_166] :
      ( k2_relset_1(A_164,B_165,C_166) = k2_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1035,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1025])).

tff(c_1049,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1035])).

tff(c_707,plain,(
    ! [A_131] :
      ( k1_relat_1(k2_funct_1(A_131)) = k2_relat_1(A_131)
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_403,plain,(
    ! [B_89,A_90] :
      ( v4_relat_1(B_89,A_90)
      | ~ r1_tarski(k1_relat_1(B_89),A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_412,plain,(
    ! [B_89] :
      ( v4_relat_1(B_89,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_403])).

tff(c_2854,plain,(
    ! [A_277] :
      ( v4_relat_1(k2_funct_1(A_277),k2_relat_1(A_277))
      | ~ v1_relat_1(k2_funct_1(A_277))
      | ~ v2_funct_1(A_277)
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_412])).

tff(c_2859,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_2854])).

tff(c_2865,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_2859])).

tff(c_2866,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2865])).

tff(c_2869,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_2866])).

tff(c_2873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_2869])).

tff(c_2875,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2865])).

tff(c_211,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2874,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2865])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3664,plain,(
    ! [A_314,A_315] :
      ( r1_tarski(k2_relat_1(A_314),A_315)
      | ~ v4_relat_1(k2_funct_1(A_314),A_315)
      | ~ v1_relat_1(k2_funct_1(A_314))
      | ~ v2_funct_1(A_314)
      | ~ v1_funct_1(A_314)
      | ~ v1_relat_1(A_314) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_26])).

tff(c_3686,plain,(
    ! [A_316] :
      ( r1_tarski(k2_relat_1(A_316),k1_relat_1(k2_funct_1(A_316)))
      | ~ v2_funct_1(A_316)
      | ~ v1_funct_1(A_316)
      | ~ v1_relat_1(A_316)
      | ~ v1_relat_1(k2_funct_1(A_316)) ) ),
    inference(resolution,[status(thm)],[c_412,c_3664])).

tff(c_3697,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_3686])).

tff(c_3708,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_229,c_82,c_76,c_3697])).

tff(c_367,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k1_relat_1(B_83),A_84)
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_390,plain,(
    ! [B_83,A_84] :
      ( k1_relat_1(B_83) = A_84
      | ~ r1_tarski(A_84,k1_relat_1(B_83))
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_367,c_2])).

tff(c_3712,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3708,c_390])).

tff(c_3723,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_2874,c_3712])).

tff(c_1436,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k1_relset_1(A_206,B_205,C_207) = A_206
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1449,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1436])).

tff(c_1467,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_833,c_1449])).

tff(c_1471,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1467])).

tff(c_30,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1066,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_30])).

tff(c_1078,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_1066])).

tff(c_1479,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1078])).

tff(c_28,plain,(
    ! [A_14] :
      ( k9_relat_1(A_14,k1_relat_1(A_14)) = k2_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3832,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3723,c_28])).

tff(c_3907,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_3832])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(k2_funct_1(B_21),A_20) = k10_relat_1(B_21,A_20)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3920,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3907,c_38])).

tff(c_3927,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_1479,c_3920])).

tff(c_870,plain,(
    ! [A_147] :
      ( m1_subset_1(A_147,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_147),k2_relat_1(A_147))))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_908,plain,(
    ! [A_147] :
      ( r1_tarski(A_147,k2_zfmisc_1(k1_relat_1(A_147),k2_relat_1(A_147)))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_870,c_18])).

tff(c_3977,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3927,c_908])).

tff(c_4011,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_211,c_3723,c_3977])).

tff(c_4013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_4011])).

tff(c_4014,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1467])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4058,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4055,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_4014,c_12])).

tff(c_1054,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_908])).

tff(c_1070,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_1054])).

tff(c_1113,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1070,c_2])).

tff(c_1298,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_4312,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_1298])).

tff(c_4322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4058,c_4312])).

tff(c_4323,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_4519,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4516,c_4323])).

tff(c_120,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_120])).

tff(c_156,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_156])).

tff(c_402,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_4601,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4519,c_402])).

tff(c_4606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4601])).

tff(c_4607,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4512])).

tff(c_4649,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4607,c_8])).

tff(c_4646,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4607,c_4607,c_12])).

tff(c_4836,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_402])).

tff(c_4841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_4836])).

tff(c_4842,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_4845,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4842,c_78])).

tff(c_5691,plain,(
    ! [A_440,B_441,C_442] :
      ( k2_relset_1(A_440,B_441,C_442) = k2_relat_1(C_442)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5855,plain,(
    ! [C_461] :
      ( k2_relset_1('#skF_1','#skF_2',C_461) = k2_relat_1(C_461)
      | ~ m1_subset_1(C_461,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_5691])).

tff(c_5858,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4845,c_5855])).

tff(c_5868,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5858])).

tff(c_42,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_311,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_329,plain,(
    ! [A_7,B_73,A_74] :
      ( v5_relat_1(A_7,B_73)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_74,B_73)) ) ),
    inference(resolution,[status(thm)],[c_20,c_311])).

tff(c_5287,plain,(
    ! [B_396,B_397,A_398] :
      ( v5_relat_1(k1_relat_1(B_396),B_397)
      | ~ v4_relat_1(B_396,k2_zfmisc_1(A_398,B_397))
      | ~ v1_relat_1(B_396) ) ),
    inference(resolution,[status(thm)],[c_367,c_329])).

tff(c_5386,plain,(
    ! [B_413] :
      ( v5_relat_1(k1_relat_1(B_413),'#skF_2')
      | ~ v4_relat_1(B_413,'#skF_3')
      | ~ v1_relat_1(B_413) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_5287])).

tff(c_5389,plain,(
    ! [A_22] :
      ( v5_relat_1(k2_relat_1(A_22),'#skF_2')
      | ~ v4_relat_1(k2_funct_1(A_22),'#skF_3')
      | ~ v1_relat_1(k2_funct_1(A_22))
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5386])).

tff(c_5875,plain,
    ( v5_relat_1('#skF_2','#skF_2')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5868,c_5389])).

tff(c_5894,plain,
    ( v5_relat_1('#skF_2','#skF_2')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_5875])).

tff(c_6016,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5894])).

tff(c_6019,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_6016])).

tff(c_6023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_6019])).

tff(c_6025,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5894])).

tff(c_5349,plain,(
    ! [A_406,B_407,C_408] :
      ( k1_relset_1(A_406,B_407,C_408) = k1_relat_1(C_408)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_5395,plain,(
    ! [C_414] :
      ( k1_relset_1('#skF_1','#skF_2',C_414) = k1_relat_1(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_5349])).

tff(c_5407,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4845,c_5395])).

tff(c_6916,plain,(
    ! [B_524,A_525,C_526] :
      ( k1_xboole_0 = B_524
      | k1_relset_1(A_525,B_524,C_526) = A_525
      | ~ v1_funct_2(C_526,A_525,B_524)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(A_525,B_524))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6925,plain,(
    ! [C_526] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_526) = '#skF_1'
      | ~ v1_funct_2(C_526,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_526,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_6916])).

tff(c_6973,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6925])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4865,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_10])).

tff(c_4913,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4865])).

tff(c_7004,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6973,c_4913])).

tff(c_7268,plain,(
    ! [A_538] : k2_zfmisc_1(A_538,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6973,c_6973,c_12])).

tff(c_6375,plain,(
    ! [B_502,C_503,A_504] :
      ( k1_xboole_0 = B_502
      | v1_funct_2(C_503,A_504,B_502)
      | k1_relset_1(A_504,B_502,C_503) != A_504
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6384,plain,(
    ! [C_503] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_503,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_503) != '#skF_1'
      | ~ m1_subset_1(C_503,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_6375])).

tff(c_6485,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6384])).

tff(c_6532,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_8])).

tff(c_6529,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6485,c_6485,c_12])).

tff(c_5468,plain,(
    ! [A_422] :
      ( m1_subset_1(A_422,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_422),k2_relat_1(A_422))))
      | ~ v1_funct_1(A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5506,plain,(
    ! [A_422] :
      ( r1_tarski(A_422,k2_zfmisc_1(k1_relat_1(A_422),k2_relat_1(A_422)))
      | ~ v1_funct_1(A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(resolution,[status(thm)],[c_5468,c_18])).

tff(c_5878,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5868,c_5506])).

tff(c_5896,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_5878])).

tff(c_5936,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5896,c_2])).

tff(c_6248,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5936])).

tff(c_6719,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6529,c_6248])).

tff(c_6725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6532,c_6719])).

tff(c_6727,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6384])).

tff(c_6728,plain,(
    ! [B_516,A_517,C_518] :
      ( k1_xboole_0 = B_516
      | k1_relset_1(A_517,B_516,C_518) = A_517
      | ~ v1_funct_2(C_518,A_517,B_516)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(A_517,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6737,plain,(
    ! [C_518] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_518) = '#skF_1'
      | ~ v1_funct_2(C_518,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_518,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4842,c_6728])).

tff(c_6791,plain,(
    ! [C_521] :
      ( k1_relset_1('#skF_1','#skF_2',C_521) = '#skF_1'
      | ~ v1_funct_2(C_521,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_521,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6727,c_6737])).

tff(c_6794,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4845,c_6791])).

tff(c_6805,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5407,c_6794])).

tff(c_6809,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6805,c_6248])).

tff(c_6821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4842,c_6809])).

tff(c_6822,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5936])).

tff(c_7281,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7268,c_6822])).

tff(c_7416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7004,c_7281])).

tff(c_7737,plain,(
    ! [C_557] :
      ( k1_relset_1('#skF_1','#skF_2',C_557) = '#skF_1'
      | ~ v1_funct_2(C_557,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_557,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_6925])).

tff(c_7740,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4845,c_7737])).

tff(c_7751,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5407,c_7740])).

tff(c_5890,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5868,c_30])).

tff(c_5904,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_5890])).

tff(c_7769,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7751,c_5904])).

tff(c_5249,plain,(
    ! [A_394] :
      ( k1_relat_1(k2_funct_1(A_394)) = k2_relat_1(A_394)
      | ~ v2_funct_1(A_394)
      | ~ v1_funct_1(A_394)
      | ~ v1_relat_1(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9469,plain,(
    ! [A_606] :
      ( k9_relat_1(k2_funct_1(A_606),k2_relat_1(A_606)) = k2_relat_1(k2_funct_1(A_606))
      | ~ v1_relat_1(k2_funct_1(A_606))
      | ~ v2_funct_1(A_606)
      | ~ v1_funct_1(A_606)
      | ~ v1_relat_1(A_606) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5249,c_28])).

tff(c_9485,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5868,c_9469])).

tff(c_9492,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_6025,c_9485])).

tff(c_9496,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9492,c_38])).

tff(c_9503,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_7769,c_9496])).

tff(c_9529,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9503,c_5506])).

tff(c_9563,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6025,c_211,c_9529])).

tff(c_9625,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_9563])).

tff(c_9646,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_5868,c_9625])).

tff(c_9648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_9646])).

tff(c_9650,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4865])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9663,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_9650,c_14])).

tff(c_9649,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4865])).

tff(c_9740,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_9650,c_9649])).

tff(c_9741,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9740])).

tff(c_9745,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9741,c_273])).

tff(c_9749,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9663,c_9745])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9664,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_16])).

tff(c_10566,plain,(
    ! [A_720,B_721,C_722] :
      ( k2_relset_1(A_720,B_721,C_722) = k2_relat_1(C_722)
      | ~ m1_subset_1(C_722,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10587,plain,(
    ! [A_723,B_724] : k2_relset_1(A_723,B_724,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_9664,c_10566])).

tff(c_9747,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9741,c_9741,c_74])).

tff(c_10591,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10587,c_9747])).

tff(c_10015,plain,(
    ! [A_648] :
      ( k1_relat_1(k2_funct_1(A_648)) = k2_relat_1(A_648)
      | ~ v2_funct_1(A_648)
      | ~ v1_funct_1(A_648)
      | ~ v1_relat_1(A_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11716,plain,(
    ! [A_792] :
      ( k9_relat_1(k2_funct_1(A_792),k2_relat_1(A_792)) = k2_relat_1(k2_funct_1(A_792))
      | ~ v1_relat_1(k2_funct_1(A_792))
      | ~ v2_funct_1(A_792)
      | ~ v1_funct_1(A_792)
      | ~ v1_relat_1(A_792) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10015,c_28])).

tff(c_11732,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10591,c_11716])).

tff(c_11739,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_11732])).

tff(c_11740,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11739])).

tff(c_11743,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_11740])).

tff(c_11747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_11743])).

tff(c_11749,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11739])).

tff(c_9662,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_9650,c_12])).

tff(c_283,plain,(
    ! [A_67,A_68,B_69] :
      ( v1_relat_1(A_67)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_68,B_69)) ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_301,plain,(
    ! [A_68,B_69] : v1_relat_1(k2_zfmisc_1(A_68,B_69)) ),
    inference(resolution,[status(thm)],[c_6,c_283])).

tff(c_9812,plain,(
    ! [C_615,A_616,B_617] :
      ( v4_relat_1(C_615,A_616)
      | ~ m1_subset_1(C_615,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_9912,plain,(
    ! [A_639,A_640,B_641] :
      ( v4_relat_1(A_639,A_640)
      | ~ r1_tarski(A_639,k2_zfmisc_1(A_640,B_641)) ) ),
    inference(resolution,[status(thm)],[c_20,c_9812])).

tff(c_9934,plain,(
    ! [A_640,B_641] : v4_relat_1(k2_zfmisc_1(A_640,B_641),A_640) ),
    inference(resolution,[status(thm)],[c_6,c_9912])).

tff(c_168,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_389,plain,(
    ! [B_83] :
      ( k1_relat_1(B_83) = k1_xboole_0
      | ~ v4_relat_1(B_83,k1_xboole_0)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_367,c_168])).

tff(c_9944,plain,(
    ! [B_644] :
      ( k1_relat_1(B_644) = '#skF_3'
      | ~ v4_relat_1(B_644,'#skF_3')
      | ~ v1_relat_1(B_644) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_9650,c_389])).

tff(c_9948,plain,(
    ! [B_641] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_641)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_641)) ) ),
    inference(resolution,[status(thm)],[c_9934,c_9944])).

tff(c_9959,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_9663,c_9948])).

tff(c_10613,plain,
    ( k10_relat_1('#skF_3','#skF_3') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10591,c_30])).

tff(c_10623,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_9959,c_10613])).

tff(c_11748,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11739])).

tff(c_11753,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11748,c_38])).

tff(c_11760,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_10623,c_11753])).

tff(c_10456,plain,(
    ! [A_709] :
      ( m1_subset_1(A_709,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_709),k2_relat_1(A_709))))
      | ~ v1_funct_1(A_709)
      | ~ v1_relat_1(A_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10494,plain,(
    ! [A_709] :
      ( r1_tarski(A_709,k2_zfmisc_1(k1_relat_1(A_709),k2_relat_1(A_709)))
      | ~ v1_funct_1(A_709)
      | ~ v1_relat_1(A_709) ) ),
    inference(resolution,[status(thm)],[c_10456,c_18])).

tff(c_11780,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11760,c_10494])).

tff(c_11810,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11749,c_211,c_9662,c_11780])).

tff(c_11812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9749,c_11810])).

tff(c_11813,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9740])).

tff(c_11870,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_11813,c_9662])).

tff(c_11826,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_244])).

tff(c_12034,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11870,c_11826])).

tff(c_12038,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_12034])).

tff(c_11827,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_229])).

tff(c_11832,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_82])).

tff(c_11831,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_76])).

tff(c_11899,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_9664])).

tff(c_12328,plain,(
    ! [A_843,B_844,C_845] :
      ( k2_relset_1(A_843,B_844,C_845) = k2_relat_1(C_845)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(A_843,B_844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12349,plain,(
    ! [A_846,B_847] : k2_relset_1(A_846,B_847,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_11899,c_12328])).

tff(c_11829,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_74])).

tff(c_12353,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_12349,c_11829])).

tff(c_12069,plain,(
    ! [A_817] :
      ( k1_relat_1(k2_funct_1(A_817)) = k2_relat_1(A_817)
      | ~ v2_funct_1(A_817)
      | ~ v1_funct_1(A_817)
      | ~ v1_relat_1(A_817) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14023,plain,(
    ! [A_985] :
      ( k9_relat_1(k2_funct_1(A_985),k2_relat_1(A_985)) = k2_relat_1(k2_funct_1(A_985))
      | ~ v1_relat_1(k2_funct_1(A_985))
      | ~ v2_funct_1(A_985)
      | ~ v1_funct_1(A_985)
      | ~ v1_relat_1(A_985) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12069,c_28])).

tff(c_14039,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12353,c_14023])).

tff(c_14046,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11827,c_11832,c_11831,c_14039])).

tff(c_14047,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_14046])).

tff(c_14050,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_14047])).

tff(c_14054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11827,c_11832,c_14050])).

tff(c_14056,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14046])).

tff(c_11828,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_211])).

tff(c_11816,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_11813,c_9663])).

tff(c_11842,plain,(
    ! [C_793,A_794,B_795] :
      ( v4_relat_1(C_793,A_794)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_794,B_795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_12161,plain,(
    ! [A_829,A_830,B_831] :
      ( v4_relat_1(A_829,A_830)
      | ~ r1_tarski(A_829,k2_zfmisc_1(A_830,B_831)) ) ),
    inference(resolution,[status(thm)],[c_20,c_11842])).

tff(c_12183,plain,(
    ! [A_830,B_831] : v4_relat_1(k2_zfmisc_1(A_830,B_831),A_830) ),
    inference(resolution,[status(thm)],[c_6,c_12161])).

tff(c_9652,plain,(
    ! [B_83] :
      ( k1_relat_1(B_83) = '#skF_3'
      | ~ v4_relat_1(B_83,'#skF_3')
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9650,c_9650,c_389])).

tff(c_12195,plain,(
    ! [B_834] :
      ( k1_relat_1(B_834) = '#skF_1'
      | ~ v4_relat_1(B_834,'#skF_1')
      | ~ v1_relat_1(B_834) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11813,c_11813,c_9652])).

tff(c_12199,plain,(
    ! [B_831] :
      ( k1_relat_1(k2_zfmisc_1('#skF_1',B_831)) = '#skF_1'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_831)) ) ),
    inference(resolution,[status(thm)],[c_12183,c_12195])).

tff(c_12210,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_11816,c_12199])).

tff(c_12376,plain,
    ( k10_relat_1('#skF_1','#skF_2') = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12353,c_30])).

tff(c_12386,plain,(
    k10_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11827,c_12210,c_12376])).

tff(c_14055,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14046])).

tff(c_14060,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k10_relat_1('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14055,c_38])).

tff(c_14067,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11827,c_11832,c_11831,c_12386,c_14060])).

tff(c_12249,plain,(
    ! [A_835] :
      ( m1_subset_1(A_835,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_835),k2_relat_1(A_835))))
      | ~ v1_funct_1(A_835)
      | ~ v1_relat_1(A_835) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12283,plain,(
    ! [A_835] :
      ( r1_tarski(A_835,k2_zfmisc_1(k1_relat_1(A_835),k2_relat_1(A_835)))
      | ~ v1_funct_1(A_835)
      | ~ v1_relat_1(A_835) ) ),
    inference(resolution,[status(thm)],[c_12249,c_18])).

tff(c_14087,plain,
    ( r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14067,c_12283])).

tff(c_14117,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14056,c_11828,c_11870,c_14087])).

tff(c_14119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12038,c_14117])).

tff(c_14120,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_14819,plain,(
    ! [A_1072,B_1073,C_1074] :
      ( k2_relset_1(A_1072,B_1073,C_1074) = k2_relat_1(C_1074)
      | ~ m1_subset_1(C_1074,k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1073))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_14832,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_14819])).

tff(c_14847,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14832])).

tff(c_14121,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_14912,plain,(
    ! [A_1077,B_1078,C_1079] :
      ( k1_relset_1(A_1077,B_1078,C_1079) = k1_relat_1(C_1079)
      | ~ m1_subset_1(C_1079,k1_zfmisc_1(k2_zfmisc_1(A_1077,B_1078))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14937,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14121,c_14912])).

tff(c_15410,plain,(
    ! [B_1130,C_1131,A_1132] :
      ( k1_xboole_0 = B_1130
      | v1_funct_2(C_1131,A_1132,B_1130)
      | k1_relset_1(A_1132,B_1130,C_1131) != A_1132
      | ~ m1_subset_1(C_1131,k1_zfmisc_1(k2_zfmisc_1(A_1132,B_1130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_15419,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_14121,c_15410])).

tff(c_15442,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14937,c_15419])).

tff(c_15443,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14120,c_15442])).

tff(c_15450,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_15443])).

tff(c_15453,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_15450])).

tff(c_15456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_14847,c_15453])).

tff(c_15457,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15443])).

tff(c_15501,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15457,c_8])).

tff(c_15499,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15457,c_15457,c_14])).

tff(c_14184,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_15710,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15499,c_14184])).

tff(c_15715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15501,c_15710])).

tff(c_15716,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_15726,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15716,c_78])).

tff(c_19329,plain,(
    ! [A_1434,B_1435,C_1436] :
      ( k2_relset_1(A_1434,B_1435,C_1436) = k2_relat_1(C_1436)
      | ~ m1_subset_1(C_1436,k1_zfmisc_1(k2_zfmisc_1(A_1434,B_1435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_19388,plain,(
    ! [C_1443] :
      ( k2_relset_1('#skF_1','#skF_2',C_1443) = k2_relat_1(C_1443)
      | ~ m1_subset_1(C_1443,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_19329])).

tff(c_19391,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15726,c_19388])).

tff(c_19401,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_19391])).

tff(c_44,plain,(
    ! [C_25,A_23,B_24] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14153,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14121,c_44])).

tff(c_19179,plain,(
    ! [A_1417,B_1418,C_1419] :
      ( k1_relset_1(A_1417,B_1418,C_1419) = k1_relat_1(C_1419)
      | ~ m1_subset_1(C_1419,k1_zfmisc_1(k2_zfmisc_1(A_1417,B_1418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_19514,plain,(
    ! [C_1446] :
      ( k1_relset_1('#skF_1','#skF_2',C_1446) = k1_relat_1(C_1446)
      | ~ m1_subset_1(C_1446,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_19179])).

tff(c_19526,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15726,c_19514])).

tff(c_20048,plain,(
    ! [B_1503,C_1504,A_1505] :
      ( k1_xboole_0 = B_1503
      | v1_funct_2(C_1504,A_1505,B_1503)
      | k1_relset_1(A_1505,B_1503,C_1504) != A_1505
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(k2_zfmisc_1(A_1505,B_1503))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20060,plain,(
    ! [C_1504] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_1504,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_1504) != '#skF_1'
      | ~ m1_subset_1(C_1504,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_20048])).

tff(c_20856,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20060])).

tff(c_16693,plain,(
    ! [A_1258,B_1259,C_1260] :
      ( k2_relset_1(A_1258,B_1259,C_1260) = k2_relat_1(C_1260)
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(k2_zfmisc_1(A_1258,B_1259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16742,plain,(
    ! [C_1265] :
      ( k2_relset_1('#skF_1','#skF_2',C_1265) = k2_relat_1(C_1265)
      | ~ m1_subset_1(C_1265,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_16693])).

tff(c_16745,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15726,c_16742])).

tff(c_16755,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16745])).

tff(c_16375,plain,(
    ! [A_1225,B_1226,C_1227] :
      ( k1_relset_1(A_1225,B_1226,C_1227) = k1_relat_1(C_1227)
      | ~ m1_subset_1(C_1227,k1_zfmisc_1(k2_zfmisc_1(A_1225,B_1226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16396,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14121,c_16375])).

tff(c_18045,plain,(
    ! [B_1346,C_1347,A_1348] :
      ( k1_xboole_0 = B_1346
      | v1_funct_2(C_1347,A_1348,B_1346)
      | k1_relset_1(A_1348,B_1346,C_1347) != A_1348
      | ~ m1_subset_1(C_1347,k1_zfmisc_1(k2_zfmisc_1(A_1348,B_1346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_18057,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_14121,c_18045])).

tff(c_18077,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16396,c_18057])).

tff(c_18078,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14120,c_18077])).

tff(c_18083,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18078])).

tff(c_18086,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_18083])).

tff(c_18089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_16755,c_18086])).

tff(c_18090,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18078])).

tff(c_18140,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18090,c_8])).

tff(c_18137,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18090,c_18090,c_12])).

tff(c_14154,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_14121,c_18])).

tff(c_14157,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14154,c_2])).

tff(c_16004,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14157])).

tff(c_18467,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18137,c_16004])).

tff(c_18472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18140,c_18467])).

tff(c_18473,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_14157])).

tff(c_18518,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18473,c_10])).

tff(c_18609,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18518])).

tff(c_20887,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20856,c_18609])).

tff(c_20903,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20856,c_20856,c_14])).

tff(c_21095,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20903,c_18473])).

tff(c_21097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20887,c_21095])).

tff(c_21099,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20060])).

tff(c_20756,plain,(
    ! [B_1527,A_1528,C_1529] :
      ( k1_xboole_0 = B_1527
      | k1_relset_1(A_1528,B_1527,C_1529) = A_1528
      | ~ v1_funct_2(C_1529,A_1528,B_1527)
      | ~ m1_subset_1(C_1529,k1_zfmisc_1(k2_zfmisc_1(A_1528,B_1527))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20768,plain,(
    ! [C_1529] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1529) = '#skF_1'
      | ~ v1_funct_2(C_1529,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1529,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_20756])).

tff(c_21171,plain,(
    ! [C_1543] :
      ( k1_relset_1('#skF_1','#skF_2',C_1543) = '#skF_1'
      | ~ v1_funct_2(C_1543,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1543,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_21099,c_20768])).

tff(c_21174,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_15726,c_21171])).

tff(c_21185,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_19526,c_21174])).

tff(c_19420,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19401,c_30])).

tff(c_19432,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_19420])).

tff(c_21200,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21185,c_19432])).

tff(c_18903,plain,(
    ! [A_1394] :
      ( k1_relat_1(k2_funct_1(A_1394)) = k2_relat_1(A_1394)
      | ~ v2_funct_1(A_1394)
      | ~ v1_funct_1(A_1394)
      | ~ v1_relat_1(A_1394) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_23118,plain,(
    ! [A_1594] :
      ( k9_relat_1(k2_funct_1(A_1594),k2_relat_1(A_1594)) = k2_relat_1(k2_funct_1(A_1594))
      | ~ v1_relat_1(k2_funct_1(A_1594))
      | ~ v2_funct_1(A_1594)
      | ~ v1_funct_1(A_1594)
      | ~ v1_relat_1(A_1594) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18903,c_28])).

tff(c_23134,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19401,c_23118])).

tff(c_23141,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_14153,c_23134])).

tff(c_23145,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23141,c_38])).

tff(c_23152,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_21200,c_23145])).

tff(c_68,plain,(
    ! [A_38] :
      ( v1_funct_2(A_38,k1_relat_1(A_38),k2_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_23191,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23152,c_68])).

tff(c_23221,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14153,c_211,c_23191])).

tff(c_23252,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_23221])).

tff(c_23254,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_82,c_76,c_19401,c_23252])).

tff(c_23256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14120,c_23254])).

tff(c_23257,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18518])).

tff(c_23287,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_23257])).

tff(c_15737,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15716,c_10])).

tff(c_15761,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_15737])).

tff(c_23306,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23287,c_15761])).

tff(c_23314,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23287,c_23287,c_14])).

tff(c_23435,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23314,c_15716])).

tff(c_23437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23306,c_23435])).

tff(c_23438,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_23257])).

tff(c_23448,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23438,c_15761])).

tff(c_23637,plain,(
    ! [A_1615] : k2_zfmisc_1(A_1615,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23438,c_23438,c_12])).

tff(c_23662,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_23637,c_15716])).

tff(c_23681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23448,c_23662])).

tff(c_23683,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15737])).

tff(c_23691,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_23683,c_14])).

tff(c_23803,plain,(
    ! [C_1622,A_1623,B_1624] :
      ( v4_relat_1(C_1622,A_1623)
      | ~ m1_subset_1(C_1622,k1_zfmisc_1(k2_zfmisc_1(A_1623,B_1624))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_24014,plain,(
    ! [A_1655,A_1656,B_1657] :
      ( v4_relat_1(A_1655,A_1656)
      | ~ r1_tarski(A_1655,k2_zfmisc_1(A_1656,B_1657)) ) ),
    inference(resolution,[status(thm)],[c_20,c_23803])).

tff(c_24036,plain,(
    ! [A_1656,B_1657] : v4_relat_1(k2_zfmisc_1(A_1656,B_1657),A_1656) ),
    inference(resolution,[status(thm)],[c_6,c_24014])).

tff(c_23946,plain,(
    ! [B_1642,A_1643] :
      ( r1_tarski(k1_relat_1(B_1642),A_1643)
      | ~ v4_relat_1(B_1642,A_1643)
      | ~ v1_relat_1(B_1642) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23686,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_23683,c_168])).

tff(c_24058,plain,(
    ! [B_1663] :
      ( k1_relat_1(B_1663) = '#skF_3'
      | ~ v4_relat_1(B_1663,'#skF_3')
      | ~ v1_relat_1(B_1663) ) ),
    inference(resolution,[status(thm)],[c_23946,c_23686])).

tff(c_24062,plain,(
    ! [B_1657] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_1657)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_1657)) ) ),
    inference(resolution,[status(thm)],[c_24036,c_24058])).

tff(c_24073,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14181,c_23691,c_24062])).

tff(c_23692,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_16])).

tff(c_24498,plain,(
    ! [A_1715,B_1716,C_1717] :
      ( k1_relset_1(A_1715,B_1716,C_1717) = k1_relat_1(C_1717)
      | ~ m1_subset_1(C_1717,k1_zfmisc_1(k2_zfmisc_1(A_1715,B_1716))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24505,plain,(
    ! [A_1715,B_1716] : k1_relset_1(A_1715,B_1716,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_23692,c_24498])).

tff(c_24514,plain,(
    ! [A_1715,B_1716] : k1_relset_1(A_1715,B_1716,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24073,c_24505])).

tff(c_60,plain,(
    ! [B_36,C_37,A_35] :
      ( k1_xboole_0 = B_36
      | v1_funct_2(C_37,A_35,B_36)
      | k1_relset_1(A_35,B_36,C_37) != A_35
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_24984,plain,(
    ! [B_1767,C_1768,A_1769] :
      ( B_1767 = '#skF_3'
      | v1_funct_2(C_1768,A_1769,B_1767)
      | k1_relset_1(A_1769,B_1767,C_1768) != A_1769
      | ~ m1_subset_1(C_1768,k1_zfmisc_1(k2_zfmisc_1(A_1769,B_1767))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_60])).

tff(c_24994,plain,(
    ! [B_1767,A_1769] :
      ( B_1767 = '#skF_3'
      | v1_funct_2('#skF_3',A_1769,B_1767)
      | k1_relset_1(A_1769,B_1767,'#skF_3') != A_1769 ) ),
    inference(resolution,[status(thm)],[c_23692,c_24984])).

tff(c_25008,plain,(
    ! [B_1770,A_1771] :
      ( B_1770 = '#skF_3'
      | v1_funct_2('#skF_3',A_1771,B_1770)
      | A_1771 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24514,c_24994])).

tff(c_23682,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15737])).

tff(c_23715,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_23683,c_23682])).

tff(c_23716,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_23715])).

tff(c_23728,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23716,c_14121])).

tff(c_23833,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23691,c_23728])).

tff(c_23842,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_23833,c_18])).

tff(c_23851,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_23842,c_23686])).

tff(c_23729,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23716,c_14120])).

tff(c_23859,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23851,c_23729])).

tff(c_25025,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_25008,c_23859])).

tff(c_23731,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23716,c_80])).

tff(c_25070,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25025,c_25025,c_23731])).

tff(c_25064,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25025,c_25025,c_23859])).

tff(c_25266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25070,c_25064])).

tff(c_25267,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_23715])).

tff(c_25268,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_23715])).

tff(c_25288,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25267,c_25268])).

tff(c_54,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_35,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_84,plain,(
    ! [A_35] :
      ( v1_funct_2(k1_xboole_0,A_35,k1_xboole_0)
      | k1_xboole_0 = A_35 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_54])).

tff(c_23689,plain,(
    ! [A_35] :
      ( v1_funct_2('#skF_3',A_35,'#skF_3')
      | A_35 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_23683,c_23683,c_84])).

tff(c_25516,plain,(
    ! [A_1799] :
      ( v1_funct_2('#skF_1',A_1799,'#skF_1')
      | A_1799 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25267,c_25267,c_25267,c_23689])).

tff(c_23690,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23683,c_23683,c_12])).

tff(c_25317,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25267,c_25267,c_23690])).

tff(c_25276,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25267,c_14121])).

tff(c_25452,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25317,c_25276])).

tff(c_25456,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_25452,c_18])).

tff(c_25402,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25267,c_25267,c_23686])).

tff(c_25467,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_25456,c_25402])).

tff(c_25277,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25267,c_14120])).

tff(c_25473,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25467,c_25277])).

tff(c_25519,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_25516,c_25473])).

tff(c_25523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25288,c_25519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 12:46:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.78/4.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.98/4.26  
% 10.98/4.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.98/4.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.98/4.26  
% 10.98/4.26  %Foreground sorts:
% 10.98/4.26  
% 10.98/4.26  
% 10.98/4.26  %Background operators:
% 10.98/4.26  
% 10.98/4.26  
% 10.98/4.26  %Foreground operators:
% 10.98/4.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.98/4.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.98/4.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.98/4.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.98/4.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.98/4.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.98/4.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.98/4.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.98/4.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.98/4.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.98/4.26  tff('#skF_2', type, '#skF_2': $i).
% 10.98/4.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.98/4.26  tff('#skF_3', type, '#skF_3': $i).
% 10.98/4.26  tff('#skF_1', type, '#skF_1': $i).
% 10.98/4.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.98/4.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.98/4.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.98/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.98/4.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.98/4.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.98/4.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.98/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.98/4.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.98/4.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.98/4.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.98/4.27  
% 11.21/4.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.21/4.31  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.21/4.31  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.21/4.31  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 11.21/4.31  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.21/4.31  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.21/4.31  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.21/4.31  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.21/4.31  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 11.21/4.31  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.21/4.31  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 11.21/4.31  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 11.21/4.31  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 11.21/4.31  tff(f_146, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 11.21/4.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.21/4.31  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.21/4.31  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.21/4.31  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.21/4.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.31  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.31  tff(c_212, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.21/4.31  tff(c_14158, plain, (![A_988, A_989, B_990]: (v1_relat_1(A_988) | ~r1_tarski(A_988, k2_zfmisc_1(A_989, B_990)))), inference(resolution, [status(thm)], [c_20, c_212])).
% 11.21/4.31  tff(c_14181, plain, (![A_989, B_990]: (v1_relat_1(k2_zfmisc_1(A_989, B_990)))), inference(resolution, [status(thm)], [c_6, c_14158])).
% 11.21/4.31  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.21/4.31  tff(c_34, plain, (![A_19]: (v1_funct_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.21/4.31  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.21/4.31  tff(c_169, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_72])).
% 11.21/4.31  tff(c_172, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_169])).
% 11.21/4.31  tff(c_175, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_172])).
% 11.21/4.31  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.21/4.31  tff(c_189, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.21/4.31  tff(c_196, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_189])).
% 11.21/4.31  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_196])).
% 11.21/4.31  tff(c_210, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 11.21/4.31  tff(c_244, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_210])).
% 11.21/4.31  tff(c_273, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_244])).
% 11.21/4.31  tff(c_229, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_212])).
% 11.21/4.31  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.21/4.31  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.21/4.31  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.21/4.31  tff(c_814, plain, (![A_140, B_141, C_142]: (k1_relset_1(A_140, B_141, C_142)=k1_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.21/4.31  tff(c_833, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_814])).
% 11.21/4.31  tff(c_4484, plain, (![B_336, A_337, C_338]: (k1_xboole_0=B_336 | k1_relset_1(A_337, B_336, C_338)=A_337 | ~v1_funct_2(C_338, A_337, B_336) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_337, B_336))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_4497, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_4484])).
% 11.21/4.31  tff(c_4512, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_833, c_4497])).
% 11.21/4.31  tff(c_4516, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4512])).
% 11.21/4.31  tff(c_36, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.21/4.31  tff(c_1025, plain, (![A_164, B_165, C_166]: (k2_relset_1(A_164, B_165, C_166)=k2_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_1035, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1025])).
% 11.21/4.31  tff(c_1049, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1035])).
% 11.21/4.31  tff(c_707, plain, (![A_131]: (k1_relat_1(k2_funct_1(A_131))=k2_relat_1(A_131) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.31  tff(c_403, plain, (![B_89, A_90]: (v4_relat_1(B_89, A_90) | ~r1_tarski(k1_relat_1(B_89), A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.31  tff(c_412, plain, (![B_89]: (v4_relat_1(B_89, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_6, c_403])).
% 11.21/4.31  tff(c_2854, plain, (![A_277]: (v4_relat_1(k2_funct_1(A_277), k2_relat_1(A_277)) | ~v1_relat_1(k2_funct_1(A_277)) | ~v2_funct_1(A_277) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(superposition, [status(thm), theory('equality')], [c_707, c_412])).
% 11.21/4.31  tff(c_2859, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_2854])).
% 11.21/4.31  tff(c_2865, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_2859])).
% 11.21/4.31  tff(c_2866, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2865])).
% 11.21/4.31  tff(c_2869, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_2866])).
% 11.21/4.31  tff(c_2873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_2869])).
% 11.21/4.31  tff(c_2875, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2865])).
% 11.21/4.31  tff(c_211, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_72])).
% 11.21/4.31  tff(c_2874, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_2865])).
% 11.21/4.31  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.31  tff(c_3664, plain, (![A_314, A_315]: (r1_tarski(k2_relat_1(A_314), A_315) | ~v4_relat_1(k2_funct_1(A_314), A_315) | ~v1_relat_1(k2_funct_1(A_314)) | ~v2_funct_1(A_314) | ~v1_funct_1(A_314) | ~v1_relat_1(A_314))), inference(superposition, [status(thm), theory('equality')], [c_707, c_26])).
% 11.21/4.31  tff(c_3686, plain, (![A_316]: (r1_tarski(k2_relat_1(A_316), k1_relat_1(k2_funct_1(A_316))) | ~v2_funct_1(A_316) | ~v1_funct_1(A_316) | ~v1_relat_1(A_316) | ~v1_relat_1(k2_funct_1(A_316)))), inference(resolution, [status(thm)], [c_412, c_3664])).
% 11.21/4.31  tff(c_3697, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1049, c_3686])).
% 11.21/4.31  tff(c_3708, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_229, c_82, c_76, c_3697])).
% 11.21/4.31  tff(c_367, plain, (![B_83, A_84]: (r1_tarski(k1_relat_1(B_83), A_84) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.31  tff(c_390, plain, (![B_83, A_84]: (k1_relat_1(B_83)=A_84 | ~r1_tarski(A_84, k1_relat_1(B_83)) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_367, c_2])).
% 11.21/4.31  tff(c_3712, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3708, c_390])).
% 11.21/4.31  tff(c_3723, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_2874, c_3712])).
% 11.21/4.31  tff(c_1436, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k1_relset_1(A_206, B_205, C_207)=A_206 | ~v1_funct_2(C_207, A_206, B_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_1449, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_1436])).
% 11.21/4.31  tff(c_1467, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_833, c_1449])).
% 11.21/4.31  tff(c_1471, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1467])).
% 11.21/4.31  tff(c_30, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.31  tff(c_1066, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_30])).
% 11.21/4.31  tff(c_1078, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_1066])).
% 11.21/4.31  tff(c_1479, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1078])).
% 11.21/4.31  tff(c_28, plain, (![A_14]: (k9_relat_1(A_14, k1_relat_1(A_14))=k2_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.21/4.31  tff(c_3832, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3723, c_28])).
% 11.21/4.31  tff(c_3907, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_3832])).
% 11.21/4.31  tff(c_38, plain, (![B_21, A_20]: (k9_relat_1(k2_funct_1(B_21), A_20)=k10_relat_1(B_21, A_20) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.31  tff(c_3920, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3907, c_38])).
% 11.21/4.31  tff(c_3927, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_1479, c_3920])).
% 11.21/4.31  tff(c_870, plain, (![A_147]: (m1_subset_1(A_147, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_147), k2_relat_1(A_147)))) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.21/4.31  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.31  tff(c_908, plain, (![A_147]: (r1_tarski(A_147, k2_zfmisc_1(k1_relat_1(A_147), k2_relat_1(A_147))) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_870, c_18])).
% 11.21/4.31  tff(c_3977, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3927, c_908])).
% 11.21/4.31  tff(c_4011, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_211, c_3723, c_3977])).
% 11.21/4.31  tff(c_4013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_4011])).
% 11.21/4.31  tff(c_4014, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1467])).
% 11.21/4.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.21/4.31  tff(c_4058, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_8])).
% 11.21/4.31  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.31  tff(c_4055, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_4014, c_12])).
% 11.21/4.31  tff(c_1054, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_908])).
% 11.21/4.31  tff(c_1070, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_1054])).
% 11.21/4.31  tff(c_1113, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1070, c_2])).
% 11.21/4.31  tff(c_1298, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1113])).
% 11.21/4.31  tff(c_4312, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4055, c_1298])).
% 11.21/4.31  tff(c_4322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4058, c_4312])).
% 11.21/4.31  tff(c_4323, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1113])).
% 11.21/4.31  tff(c_4519, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4516, c_4323])).
% 11.21/4.31  tff(c_120, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.31  tff(c_131, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_120])).
% 11.21/4.31  tff(c_156, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.31  tff(c_163, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_131, c_156])).
% 11.21/4.31  tff(c_402, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_163])).
% 11.21/4.31  tff(c_4601, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4519, c_402])).
% 11.21/4.31  tff(c_4606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4601])).
% 11.21/4.31  tff(c_4607, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4512])).
% 11.21/4.31  tff(c_4649, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4607, c_8])).
% 11.21/4.31  tff(c_4646, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4607, c_4607, c_12])).
% 11.21/4.31  tff(c_4836, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_402])).
% 11.21/4.31  tff(c_4841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4649, c_4836])).
% 11.21/4.31  tff(c_4842, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 11.21/4.31  tff(c_4845, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4842, c_78])).
% 11.21/4.31  tff(c_5691, plain, (![A_440, B_441, C_442]: (k2_relset_1(A_440, B_441, C_442)=k2_relat_1(C_442) | ~m1_subset_1(C_442, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_5855, plain, (![C_461]: (k2_relset_1('#skF_1', '#skF_2', C_461)=k2_relat_1(C_461) | ~m1_subset_1(C_461, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_5691])).
% 11.21/4.31  tff(c_5858, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4845, c_5855])).
% 11.21/4.31  tff(c_5868, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5858])).
% 11.21/4.31  tff(c_42, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.31  tff(c_311, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.21/4.31  tff(c_329, plain, (![A_7, B_73, A_74]: (v5_relat_1(A_7, B_73) | ~r1_tarski(A_7, k2_zfmisc_1(A_74, B_73)))), inference(resolution, [status(thm)], [c_20, c_311])).
% 11.21/4.31  tff(c_5287, plain, (![B_396, B_397, A_398]: (v5_relat_1(k1_relat_1(B_396), B_397) | ~v4_relat_1(B_396, k2_zfmisc_1(A_398, B_397)) | ~v1_relat_1(B_396))), inference(resolution, [status(thm)], [c_367, c_329])).
% 11.21/4.31  tff(c_5386, plain, (![B_413]: (v5_relat_1(k1_relat_1(B_413), '#skF_2') | ~v4_relat_1(B_413, '#skF_3') | ~v1_relat_1(B_413))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_5287])).
% 11.21/4.31  tff(c_5389, plain, (![A_22]: (v5_relat_1(k2_relat_1(A_22), '#skF_2') | ~v4_relat_1(k2_funct_1(A_22), '#skF_3') | ~v1_relat_1(k2_funct_1(A_22)) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5386])).
% 11.21/4.31  tff(c_5875, plain, (v5_relat_1('#skF_2', '#skF_2') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5868, c_5389])).
% 11.21/4.31  tff(c_5894, plain, (v5_relat_1('#skF_2', '#skF_2') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_5875])).
% 11.21/4.31  tff(c_6016, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5894])).
% 11.21/4.31  tff(c_6019, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_6016])).
% 11.21/4.31  tff(c_6023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_6019])).
% 11.21/4.31  tff(c_6025, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5894])).
% 11.21/4.31  tff(c_5349, plain, (![A_406, B_407, C_408]: (k1_relset_1(A_406, B_407, C_408)=k1_relat_1(C_408) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.21/4.31  tff(c_5395, plain, (![C_414]: (k1_relset_1('#skF_1', '#skF_2', C_414)=k1_relat_1(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_5349])).
% 11.21/4.31  tff(c_5407, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4845, c_5395])).
% 11.21/4.31  tff(c_6916, plain, (![B_524, A_525, C_526]: (k1_xboole_0=B_524 | k1_relset_1(A_525, B_524, C_526)=A_525 | ~v1_funct_2(C_526, A_525, B_524) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(A_525, B_524))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_6925, plain, (![C_526]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_526)='#skF_1' | ~v1_funct_2(C_526, '#skF_1', '#skF_2') | ~m1_subset_1(C_526, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_6916])).
% 11.21/4.31  tff(c_6973, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6925])).
% 11.21/4.31  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.31  tff(c_4865, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4842, c_10])).
% 11.21/4.31  tff(c_4913, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4865])).
% 11.21/4.31  tff(c_7004, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6973, c_4913])).
% 11.21/4.31  tff(c_7268, plain, (![A_538]: (k2_zfmisc_1(A_538, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6973, c_6973, c_12])).
% 11.21/4.31  tff(c_6375, plain, (![B_502, C_503, A_504]: (k1_xboole_0=B_502 | v1_funct_2(C_503, A_504, B_502) | k1_relset_1(A_504, B_502, C_503)!=A_504 | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_502))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_6384, plain, (![C_503]: (k1_xboole_0='#skF_2' | v1_funct_2(C_503, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_503)!='#skF_1' | ~m1_subset_1(C_503, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_6375])).
% 11.21/4.31  tff(c_6485, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6384])).
% 11.21/4.31  tff(c_6532, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_8])).
% 11.21/4.31  tff(c_6529, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6485, c_6485, c_12])).
% 11.21/4.31  tff(c_5468, plain, (![A_422]: (m1_subset_1(A_422, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_422), k2_relat_1(A_422)))) | ~v1_funct_1(A_422) | ~v1_relat_1(A_422))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.21/4.31  tff(c_5506, plain, (![A_422]: (r1_tarski(A_422, k2_zfmisc_1(k1_relat_1(A_422), k2_relat_1(A_422))) | ~v1_funct_1(A_422) | ~v1_relat_1(A_422))), inference(resolution, [status(thm)], [c_5468, c_18])).
% 11.21/4.31  tff(c_5878, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5868, c_5506])).
% 11.21/4.31  tff(c_5896, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_5878])).
% 11.21/4.31  tff(c_5936, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_5896, c_2])).
% 11.21/4.31  tff(c_6248, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5936])).
% 11.21/4.31  tff(c_6719, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6529, c_6248])).
% 11.21/4.31  tff(c_6725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6532, c_6719])).
% 11.21/4.31  tff(c_6727, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6384])).
% 11.21/4.31  tff(c_6728, plain, (![B_516, A_517, C_518]: (k1_xboole_0=B_516 | k1_relset_1(A_517, B_516, C_518)=A_517 | ~v1_funct_2(C_518, A_517, B_516) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(A_517, B_516))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_6737, plain, (![C_518]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_518)='#skF_1' | ~v1_funct_2(C_518, '#skF_1', '#skF_2') | ~m1_subset_1(C_518, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4842, c_6728])).
% 11.21/4.31  tff(c_6791, plain, (![C_521]: (k1_relset_1('#skF_1', '#skF_2', C_521)='#skF_1' | ~v1_funct_2(C_521, '#skF_1', '#skF_2') | ~m1_subset_1(C_521, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6727, c_6737])).
% 11.21/4.31  tff(c_6794, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4845, c_6791])).
% 11.21/4.31  tff(c_6805, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5407, c_6794])).
% 11.21/4.31  tff(c_6809, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6805, c_6248])).
% 11.21/4.31  tff(c_6821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4842, c_6809])).
% 11.21/4.31  tff(c_6822, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5936])).
% 11.21/4.31  tff(c_7281, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7268, c_6822])).
% 11.21/4.31  tff(c_7416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7004, c_7281])).
% 11.21/4.31  tff(c_7737, plain, (![C_557]: (k1_relset_1('#skF_1', '#skF_2', C_557)='#skF_1' | ~v1_funct_2(C_557, '#skF_1', '#skF_2') | ~m1_subset_1(C_557, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_6925])).
% 11.21/4.31  tff(c_7740, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4845, c_7737])).
% 11.21/4.31  tff(c_7751, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5407, c_7740])).
% 11.21/4.31  tff(c_5890, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5868, c_30])).
% 11.21/4.31  tff(c_5904, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_5890])).
% 11.21/4.31  tff(c_7769, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7751, c_5904])).
% 11.21/4.31  tff(c_5249, plain, (![A_394]: (k1_relat_1(k2_funct_1(A_394))=k2_relat_1(A_394) | ~v2_funct_1(A_394) | ~v1_funct_1(A_394) | ~v1_relat_1(A_394))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.31  tff(c_9469, plain, (![A_606]: (k9_relat_1(k2_funct_1(A_606), k2_relat_1(A_606))=k2_relat_1(k2_funct_1(A_606)) | ~v1_relat_1(k2_funct_1(A_606)) | ~v2_funct_1(A_606) | ~v1_funct_1(A_606) | ~v1_relat_1(A_606))), inference(superposition, [status(thm), theory('equality')], [c_5249, c_28])).
% 11.21/4.31  tff(c_9485, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5868, c_9469])).
% 11.21/4.31  tff(c_9492, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_6025, c_9485])).
% 11.21/4.31  tff(c_9496, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9492, c_38])).
% 11.21/4.31  tff(c_9503, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_7769, c_9496])).
% 11.21/4.31  tff(c_9529, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9503, c_5506])).
% 11.21/4.31  tff(c_9563, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6025, c_211, c_9529])).
% 11.21/4.31  tff(c_9625, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_9563])).
% 11.21/4.31  tff(c_9646, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_5868, c_9625])).
% 11.21/4.31  tff(c_9648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_9646])).
% 11.21/4.31  tff(c_9650, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4865])).
% 11.21/4.31  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.31  tff(c_9663, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_9650, c_14])).
% 11.21/4.31  tff(c_9649, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4865])).
% 11.21/4.31  tff(c_9740, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_9650, c_9649])).
% 11.21/4.31  tff(c_9741, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_9740])).
% 11.21/4.31  tff(c_9745, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9741, c_273])).
% 11.21/4.31  tff(c_9749, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9663, c_9745])).
% 11.21/4.31  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.21/4.31  tff(c_9664, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_16])).
% 11.21/4.31  tff(c_10566, plain, (![A_720, B_721, C_722]: (k2_relset_1(A_720, B_721, C_722)=k2_relat_1(C_722) | ~m1_subset_1(C_722, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_10587, plain, (![A_723, B_724]: (k2_relset_1(A_723, B_724, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_9664, c_10566])).
% 11.21/4.31  tff(c_9747, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9741, c_9741, c_74])).
% 11.21/4.31  tff(c_10591, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10587, c_9747])).
% 11.21/4.31  tff(c_10015, plain, (![A_648]: (k1_relat_1(k2_funct_1(A_648))=k2_relat_1(A_648) | ~v2_funct_1(A_648) | ~v1_funct_1(A_648) | ~v1_relat_1(A_648))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.31  tff(c_11716, plain, (![A_792]: (k9_relat_1(k2_funct_1(A_792), k2_relat_1(A_792))=k2_relat_1(k2_funct_1(A_792)) | ~v1_relat_1(k2_funct_1(A_792)) | ~v2_funct_1(A_792) | ~v1_funct_1(A_792) | ~v1_relat_1(A_792))), inference(superposition, [status(thm), theory('equality')], [c_10015, c_28])).
% 11.21/4.31  tff(c_11732, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10591, c_11716])).
% 11.21/4.31  tff(c_11739, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_11732])).
% 11.21/4.31  tff(c_11740, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_11739])).
% 11.21/4.31  tff(c_11743, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_11740])).
% 11.21/4.31  tff(c_11747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_11743])).
% 11.21/4.31  tff(c_11749, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11739])).
% 11.21/4.31  tff(c_9662, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_9650, c_12])).
% 11.21/4.31  tff(c_283, plain, (![A_67, A_68, B_69]: (v1_relat_1(A_67) | ~r1_tarski(A_67, k2_zfmisc_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_20, c_212])).
% 11.21/4.31  tff(c_301, plain, (![A_68, B_69]: (v1_relat_1(k2_zfmisc_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_6, c_283])).
% 11.21/4.31  tff(c_9812, plain, (![C_615, A_616, B_617]: (v4_relat_1(C_615, A_616) | ~m1_subset_1(C_615, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.21/4.31  tff(c_9912, plain, (![A_639, A_640, B_641]: (v4_relat_1(A_639, A_640) | ~r1_tarski(A_639, k2_zfmisc_1(A_640, B_641)))), inference(resolution, [status(thm)], [c_20, c_9812])).
% 11.21/4.31  tff(c_9934, plain, (![A_640, B_641]: (v4_relat_1(k2_zfmisc_1(A_640, B_641), A_640))), inference(resolution, [status(thm)], [c_6, c_9912])).
% 11.21/4.31  tff(c_168, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_156])).
% 11.21/4.31  tff(c_389, plain, (![B_83]: (k1_relat_1(B_83)=k1_xboole_0 | ~v4_relat_1(B_83, k1_xboole_0) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_367, c_168])).
% 11.21/4.31  tff(c_9944, plain, (![B_644]: (k1_relat_1(B_644)='#skF_3' | ~v4_relat_1(B_644, '#skF_3') | ~v1_relat_1(B_644))), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_9650, c_389])).
% 11.21/4.31  tff(c_9948, plain, (![B_641]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_641))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_641)))), inference(resolution, [status(thm)], [c_9934, c_9944])).
% 11.21/4.31  tff(c_9959, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_9663, c_9948])).
% 11.21/4.31  tff(c_10613, plain, (k10_relat_1('#skF_3', '#skF_3')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10591, c_30])).
% 11.21/4.31  tff(c_10623, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_9959, c_10613])).
% 11.21/4.31  tff(c_11748, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11739])).
% 11.21/4.31  tff(c_11753, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11748, c_38])).
% 11.21/4.31  tff(c_11760, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_10623, c_11753])).
% 11.21/4.31  tff(c_10456, plain, (![A_709]: (m1_subset_1(A_709, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_709), k2_relat_1(A_709)))) | ~v1_funct_1(A_709) | ~v1_relat_1(A_709))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.21/4.31  tff(c_10494, plain, (![A_709]: (r1_tarski(A_709, k2_zfmisc_1(k1_relat_1(A_709), k2_relat_1(A_709))) | ~v1_funct_1(A_709) | ~v1_relat_1(A_709))), inference(resolution, [status(thm)], [c_10456, c_18])).
% 11.21/4.31  tff(c_11780, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11760, c_10494])).
% 11.21/4.31  tff(c_11810, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11749, c_211, c_9662, c_11780])).
% 11.21/4.31  tff(c_11812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9749, c_11810])).
% 11.21/4.31  tff(c_11813, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_9740])).
% 11.21/4.31  tff(c_11870, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_11813, c_9662])).
% 11.21/4.31  tff(c_11826, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_244])).
% 11.21/4.31  tff(c_12034, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11870, c_11826])).
% 11.21/4.31  tff(c_12038, plain, (~r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_20, c_12034])).
% 11.21/4.31  tff(c_11827, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_229])).
% 11.21/4.31  tff(c_11832, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_82])).
% 11.21/4.31  tff(c_11831, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_76])).
% 11.21/4.31  tff(c_11899, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_9664])).
% 11.21/4.31  tff(c_12328, plain, (![A_843, B_844, C_845]: (k2_relset_1(A_843, B_844, C_845)=k2_relat_1(C_845) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(A_843, B_844))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_12349, plain, (![A_846, B_847]: (k2_relset_1(A_846, B_847, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_11899, c_12328])).
% 11.21/4.31  tff(c_11829, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_74])).
% 11.21/4.31  tff(c_12353, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_12349, c_11829])).
% 11.21/4.31  tff(c_12069, plain, (![A_817]: (k1_relat_1(k2_funct_1(A_817))=k2_relat_1(A_817) | ~v2_funct_1(A_817) | ~v1_funct_1(A_817) | ~v1_relat_1(A_817))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.31  tff(c_14023, plain, (![A_985]: (k9_relat_1(k2_funct_1(A_985), k2_relat_1(A_985))=k2_relat_1(k2_funct_1(A_985)) | ~v1_relat_1(k2_funct_1(A_985)) | ~v2_funct_1(A_985) | ~v1_funct_1(A_985) | ~v1_relat_1(A_985))), inference(superposition, [status(thm), theory('equality')], [c_12069, c_28])).
% 11.21/4.31  tff(c_14039, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12353, c_14023])).
% 11.21/4.31  tff(c_14046, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11827, c_11832, c_11831, c_14039])).
% 11.21/4.31  tff(c_14047, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_14046])).
% 11.21/4.31  tff(c_14050, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_36, c_14047])).
% 11.21/4.31  tff(c_14054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11827, c_11832, c_14050])).
% 11.21/4.31  tff(c_14056, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_14046])).
% 11.21/4.31  tff(c_11828, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_211])).
% 11.21/4.31  tff(c_11816, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_11813, c_9663])).
% 11.21/4.31  tff(c_11842, plain, (![C_793, A_794, B_795]: (v4_relat_1(C_793, A_794) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_794, B_795))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.21/4.31  tff(c_12161, plain, (![A_829, A_830, B_831]: (v4_relat_1(A_829, A_830) | ~r1_tarski(A_829, k2_zfmisc_1(A_830, B_831)))), inference(resolution, [status(thm)], [c_20, c_11842])).
% 11.21/4.31  tff(c_12183, plain, (![A_830, B_831]: (v4_relat_1(k2_zfmisc_1(A_830, B_831), A_830))), inference(resolution, [status(thm)], [c_6, c_12161])).
% 11.21/4.31  tff(c_9652, plain, (![B_83]: (k1_relat_1(B_83)='#skF_3' | ~v4_relat_1(B_83, '#skF_3') | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_9650, c_9650, c_389])).
% 11.21/4.31  tff(c_12195, plain, (![B_834]: (k1_relat_1(B_834)='#skF_1' | ~v4_relat_1(B_834, '#skF_1') | ~v1_relat_1(B_834))), inference(demodulation, [status(thm), theory('equality')], [c_11813, c_11813, c_9652])).
% 11.21/4.31  tff(c_12199, plain, (![B_831]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_831))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_831)))), inference(resolution, [status(thm)], [c_12183, c_12195])).
% 11.21/4.31  tff(c_12210, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_11816, c_12199])).
% 11.21/4.31  tff(c_12376, plain, (k10_relat_1('#skF_1', '#skF_2')=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12353, c_30])).
% 11.21/4.31  tff(c_12386, plain, (k10_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11827, c_12210, c_12376])).
% 11.21/4.31  tff(c_14055, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_14046])).
% 11.21/4.31  tff(c_14060, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k10_relat_1('#skF_1', '#skF_2') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14055, c_38])).
% 11.21/4.31  tff(c_14067, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11827, c_11832, c_11831, c_12386, c_14060])).
% 11.21/4.31  tff(c_12249, plain, (![A_835]: (m1_subset_1(A_835, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_835), k2_relat_1(A_835)))) | ~v1_funct_1(A_835) | ~v1_relat_1(A_835))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.21/4.31  tff(c_12283, plain, (![A_835]: (r1_tarski(A_835, k2_zfmisc_1(k1_relat_1(A_835), k2_relat_1(A_835))) | ~v1_funct_1(A_835) | ~v1_relat_1(A_835))), inference(resolution, [status(thm)], [c_12249, c_18])).
% 11.21/4.31  tff(c_14087, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14067, c_12283])).
% 11.21/4.31  tff(c_14117, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14056, c_11828, c_11870, c_14087])).
% 11.21/4.31  tff(c_14119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12038, c_14117])).
% 11.21/4.31  tff(c_14120, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_210])).
% 11.21/4.31  tff(c_14819, plain, (![A_1072, B_1073, C_1074]: (k2_relset_1(A_1072, B_1073, C_1074)=k2_relat_1(C_1074) | ~m1_subset_1(C_1074, k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1073))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_14832, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_14819])).
% 11.21/4.31  tff(c_14847, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_14832])).
% 11.21/4.31  tff(c_14121, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_210])).
% 11.21/4.31  tff(c_14912, plain, (![A_1077, B_1078, C_1079]: (k1_relset_1(A_1077, B_1078, C_1079)=k1_relat_1(C_1079) | ~m1_subset_1(C_1079, k1_zfmisc_1(k2_zfmisc_1(A_1077, B_1078))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.21/4.31  tff(c_14937, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14121, c_14912])).
% 11.21/4.31  tff(c_15410, plain, (![B_1130, C_1131, A_1132]: (k1_xboole_0=B_1130 | v1_funct_2(C_1131, A_1132, B_1130) | k1_relset_1(A_1132, B_1130, C_1131)!=A_1132 | ~m1_subset_1(C_1131, k1_zfmisc_1(k2_zfmisc_1(A_1132, B_1130))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_15419, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_14121, c_15410])).
% 11.21/4.31  tff(c_15442, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14937, c_15419])).
% 11.21/4.31  tff(c_15443, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14120, c_15442])).
% 11.21/4.31  tff(c_15450, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_15443])).
% 11.21/4.31  tff(c_15453, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_15450])).
% 11.21/4.31  tff(c_15456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_14847, c_15453])).
% 11.21/4.31  tff(c_15457, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_15443])).
% 11.21/4.31  tff(c_15501, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_15457, c_8])).
% 11.21/4.31  tff(c_15499, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15457, c_15457, c_14])).
% 11.21/4.31  tff(c_14184, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_163])).
% 11.21/4.31  tff(c_15710, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15499, c_14184])).
% 11.21/4.31  tff(c_15715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15501, c_15710])).
% 11.21/4.31  tff(c_15716, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_163])).
% 11.21/4.31  tff(c_15726, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15716, c_78])).
% 11.21/4.31  tff(c_19329, plain, (![A_1434, B_1435, C_1436]: (k2_relset_1(A_1434, B_1435, C_1436)=k2_relat_1(C_1436) | ~m1_subset_1(C_1436, k1_zfmisc_1(k2_zfmisc_1(A_1434, B_1435))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_19388, plain, (![C_1443]: (k2_relset_1('#skF_1', '#skF_2', C_1443)=k2_relat_1(C_1443) | ~m1_subset_1(C_1443, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15716, c_19329])).
% 11.21/4.31  tff(c_19391, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_15726, c_19388])).
% 11.21/4.31  tff(c_19401, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_19391])).
% 11.21/4.31  tff(c_44, plain, (![C_25, A_23, B_24]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.21/4.31  tff(c_14153, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14121, c_44])).
% 11.21/4.31  tff(c_19179, plain, (![A_1417, B_1418, C_1419]: (k1_relset_1(A_1417, B_1418, C_1419)=k1_relat_1(C_1419) | ~m1_subset_1(C_1419, k1_zfmisc_1(k2_zfmisc_1(A_1417, B_1418))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.21/4.31  tff(c_19514, plain, (![C_1446]: (k1_relset_1('#skF_1', '#skF_2', C_1446)=k1_relat_1(C_1446) | ~m1_subset_1(C_1446, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15716, c_19179])).
% 11.21/4.31  tff(c_19526, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_15726, c_19514])).
% 11.21/4.31  tff(c_20048, plain, (![B_1503, C_1504, A_1505]: (k1_xboole_0=B_1503 | v1_funct_2(C_1504, A_1505, B_1503) | k1_relset_1(A_1505, B_1503, C_1504)!=A_1505 | ~m1_subset_1(C_1504, k1_zfmisc_1(k2_zfmisc_1(A_1505, B_1503))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_20060, plain, (![C_1504]: (k1_xboole_0='#skF_2' | v1_funct_2(C_1504, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_1504)!='#skF_1' | ~m1_subset_1(C_1504, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15716, c_20048])).
% 11.21/4.31  tff(c_20856, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_20060])).
% 11.21/4.31  tff(c_16693, plain, (![A_1258, B_1259, C_1260]: (k2_relset_1(A_1258, B_1259, C_1260)=k2_relat_1(C_1260) | ~m1_subset_1(C_1260, k1_zfmisc_1(k2_zfmisc_1(A_1258, B_1259))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.21/4.31  tff(c_16742, plain, (![C_1265]: (k2_relset_1('#skF_1', '#skF_2', C_1265)=k2_relat_1(C_1265) | ~m1_subset_1(C_1265, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15716, c_16693])).
% 11.21/4.31  tff(c_16745, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_15726, c_16742])).
% 11.21/4.31  tff(c_16755, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16745])).
% 11.21/4.31  tff(c_16375, plain, (![A_1225, B_1226, C_1227]: (k1_relset_1(A_1225, B_1226, C_1227)=k1_relat_1(C_1227) | ~m1_subset_1(C_1227, k1_zfmisc_1(k2_zfmisc_1(A_1225, B_1226))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.21/4.31  tff(c_16396, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14121, c_16375])).
% 11.21/4.31  tff(c_18045, plain, (![B_1346, C_1347, A_1348]: (k1_xboole_0=B_1346 | v1_funct_2(C_1347, A_1348, B_1346) | k1_relset_1(A_1348, B_1346, C_1347)!=A_1348 | ~m1_subset_1(C_1347, k1_zfmisc_1(k2_zfmisc_1(A_1348, B_1346))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_18057, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_14121, c_18045])).
% 11.21/4.31  tff(c_18077, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16396, c_18057])).
% 11.21/4.31  tff(c_18078, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14120, c_18077])).
% 11.21/4.31  tff(c_18083, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_18078])).
% 11.21/4.31  tff(c_18086, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_18083])).
% 11.21/4.31  tff(c_18089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_16755, c_18086])).
% 11.21/4.31  tff(c_18090, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18078])).
% 11.21/4.31  tff(c_18140, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_18090, c_8])).
% 11.21/4.31  tff(c_18137, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18090, c_18090, c_12])).
% 11.21/4.31  tff(c_14154, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_14121, c_18])).
% 11.21/4.31  tff(c_14157, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14154, c_2])).
% 11.21/4.31  tff(c_16004, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14157])).
% 11.21/4.31  tff(c_18467, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18137, c_16004])).
% 11.21/4.31  tff(c_18472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18140, c_18467])).
% 11.21/4.31  tff(c_18473, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_14157])).
% 11.21/4.31  tff(c_18518, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18473, c_10])).
% 11.21/4.31  tff(c_18609, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_18518])).
% 11.21/4.31  tff(c_20887, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20856, c_18609])).
% 11.21/4.31  tff(c_20903, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20856, c_20856, c_14])).
% 11.21/4.31  tff(c_21095, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20903, c_18473])).
% 11.21/4.31  tff(c_21097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20887, c_21095])).
% 11.21/4.31  tff(c_21099, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_20060])).
% 11.21/4.31  tff(c_20756, plain, (![B_1527, A_1528, C_1529]: (k1_xboole_0=B_1527 | k1_relset_1(A_1528, B_1527, C_1529)=A_1528 | ~v1_funct_2(C_1529, A_1528, B_1527) | ~m1_subset_1(C_1529, k1_zfmisc_1(k2_zfmisc_1(A_1528, B_1527))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_20768, plain, (![C_1529]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1529)='#skF_1' | ~v1_funct_2(C_1529, '#skF_1', '#skF_2') | ~m1_subset_1(C_1529, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_15716, c_20756])).
% 11.21/4.31  tff(c_21171, plain, (![C_1543]: (k1_relset_1('#skF_1', '#skF_2', C_1543)='#skF_1' | ~v1_funct_2(C_1543, '#skF_1', '#skF_2') | ~m1_subset_1(C_1543, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_21099, c_20768])).
% 11.21/4.31  tff(c_21174, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_15726, c_21171])).
% 11.21/4.31  tff(c_21185, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_19526, c_21174])).
% 11.21/4.31  tff(c_19420, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19401, c_30])).
% 11.21/4.31  tff(c_19432, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_19420])).
% 11.21/4.31  tff(c_21200, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21185, c_19432])).
% 11.21/4.31  tff(c_18903, plain, (![A_1394]: (k1_relat_1(k2_funct_1(A_1394))=k2_relat_1(A_1394) | ~v2_funct_1(A_1394) | ~v1_funct_1(A_1394) | ~v1_relat_1(A_1394))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.31  tff(c_23118, plain, (![A_1594]: (k9_relat_1(k2_funct_1(A_1594), k2_relat_1(A_1594))=k2_relat_1(k2_funct_1(A_1594)) | ~v1_relat_1(k2_funct_1(A_1594)) | ~v2_funct_1(A_1594) | ~v1_funct_1(A_1594) | ~v1_relat_1(A_1594))), inference(superposition, [status(thm), theory('equality')], [c_18903, c_28])).
% 11.21/4.31  tff(c_23134, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19401, c_23118])).
% 11.21/4.31  tff(c_23141, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_14153, c_23134])).
% 11.21/4.31  tff(c_23145, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23141, c_38])).
% 11.21/4.31  tff(c_23152, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_21200, c_23145])).
% 11.21/4.31  tff(c_68, plain, (![A_38]: (v1_funct_2(A_38, k1_relat_1(A_38), k2_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 11.21/4.31  tff(c_23191, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_23152, c_68])).
% 11.21/4.31  tff(c_23221, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14153, c_211, c_23191])).
% 11.21/4.31  tff(c_23252, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_23221])).
% 11.21/4.31  tff(c_23254, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_82, c_76, c_19401, c_23252])).
% 11.21/4.31  tff(c_23256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14120, c_23254])).
% 11.21/4.31  tff(c_23257, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18518])).
% 11.21/4.31  tff(c_23287, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_23257])).
% 11.21/4.31  tff(c_15737, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15716, c_10])).
% 11.21/4.31  tff(c_15761, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_15737])).
% 11.21/4.31  tff(c_23306, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_23287, c_15761])).
% 11.21/4.31  tff(c_23314, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23287, c_23287, c_14])).
% 11.21/4.31  tff(c_23435, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_23314, c_15716])).
% 11.21/4.31  tff(c_23437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23306, c_23435])).
% 11.21/4.31  tff(c_23438, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_23257])).
% 11.21/4.31  tff(c_23448, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23438, c_15761])).
% 11.21/4.31  tff(c_23637, plain, (![A_1615]: (k2_zfmisc_1(A_1615, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_23438, c_23438, c_12])).
% 11.21/4.31  tff(c_23662, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_23637, c_15716])).
% 11.21/4.31  tff(c_23681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23448, c_23662])).
% 11.21/4.31  tff(c_23683, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_15737])).
% 11.21/4.31  tff(c_23691, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_23683, c_14])).
% 11.21/4.31  tff(c_23803, plain, (![C_1622, A_1623, B_1624]: (v4_relat_1(C_1622, A_1623) | ~m1_subset_1(C_1622, k1_zfmisc_1(k2_zfmisc_1(A_1623, B_1624))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.21/4.31  tff(c_24014, plain, (![A_1655, A_1656, B_1657]: (v4_relat_1(A_1655, A_1656) | ~r1_tarski(A_1655, k2_zfmisc_1(A_1656, B_1657)))), inference(resolution, [status(thm)], [c_20, c_23803])).
% 11.21/4.31  tff(c_24036, plain, (![A_1656, B_1657]: (v4_relat_1(k2_zfmisc_1(A_1656, B_1657), A_1656))), inference(resolution, [status(thm)], [c_6, c_24014])).
% 11.21/4.31  tff(c_23946, plain, (![B_1642, A_1643]: (r1_tarski(k1_relat_1(B_1642), A_1643) | ~v4_relat_1(B_1642, A_1643) | ~v1_relat_1(B_1642))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.31  tff(c_23686, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_23683, c_168])).
% 11.21/4.31  tff(c_24058, plain, (![B_1663]: (k1_relat_1(B_1663)='#skF_3' | ~v4_relat_1(B_1663, '#skF_3') | ~v1_relat_1(B_1663))), inference(resolution, [status(thm)], [c_23946, c_23686])).
% 11.21/4.31  tff(c_24062, plain, (![B_1657]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_1657))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_1657)))), inference(resolution, [status(thm)], [c_24036, c_24058])).
% 11.21/4.31  tff(c_24073, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14181, c_23691, c_24062])).
% 11.21/4.31  tff(c_23692, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_16])).
% 11.21/4.31  tff(c_24498, plain, (![A_1715, B_1716, C_1717]: (k1_relset_1(A_1715, B_1716, C_1717)=k1_relat_1(C_1717) | ~m1_subset_1(C_1717, k1_zfmisc_1(k2_zfmisc_1(A_1715, B_1716))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.21/4.31  tff(c_24505, plain, (![A_1715, B_1716]: (k1_relset_1(A_1715, B_1716, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_23692, c_24498])).
% 11.21/4.31  tff(c_24514, plain, (![A_1715, B_1716]: (k1_relset_1(A_1715, B_1716, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24073, c_24505])).
% 11.21/4.31  tff(c_60, plain, (![B_36, C_37, A_35]: (k1_xboole_0=B_36 | v1_funct_2(C_37, A_35, B_36) | k1_relset_1(A_35, B_36, C_37)!=A_35 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_24984, plain, (![B_1767, C_1768, A_1769]: (B_1767='#skF_3' | v1_funct_2(C_1768, A_1769, B_1767) | k1_relset_1(A_1769, B_1767, C_1768)!=A_1769 | ~m1_subset_1(C_1768, k1_zfmisc_1(k2_zfmisc_1(A_1769, B_1767))))), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_60])).
% 11.21/4.31  tff(c_24994, plain, (![B_1767, A_1769]: (B_1767='#skF_3' | v1_funct_2('#skF_3', A_1769, B_1767) | k1_relset_1(A_1769, B_1767, '#skF_3')!=A_1769)), inference(resolution, [status(thm)], [c_23692, c_24984])).
% 11.21/4.31  tff(c_25008, plain, (![B_1770, A_1771]: (B_1770='#skF_3' | v1_funct_2('#skF_3', A_1771, B_1770) | A_1771!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24514, c_24994])).
% 11.21/4.31  tff(c_23682, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_15737])).
% 11.21/4.31  tff(c_23715, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_23683, c_23682])).
% 11.21/4.31  tff(c_23716, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_23715])).
% 11.21/4.31  tff(c_23728, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23716, c_14121])).
% 11.21/4.31  tff(c_23833, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_23691, c_23728])).
% 11.21/4.31  tff(c_23842, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_23833, c_18])).
% 11.21/4.31  tff(c_23851, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_23842, c_23686])).
% 11.21/4.31  tff(c_23729, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23716, c_14120])).
% 11.21/4.31  tff(c_23859, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23851, c_23729])).
% 11.21/4.31  tff(c_25025, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_25008, c_23859])).
% 11.21/4.31  tff(c_23731, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23716, c_80])).
% 11.21/4.31  tff(c_25070, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25025, c_25025, c_23731])).
% 11.21/4.31  tff(c_25064, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25025, c_25025, c_23859])).
% 11.21/4.31  tff(c_25266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25070, c_25064])).
% 11.21/4.31  tff(c_25267, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_23715])).
% 11.21/4.31  tff(c_25268, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_23715])).
% 11.21/4.31  tff(c_25288, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25267, c_25268])).
% 11.21/4.31  tff(c_54, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_35, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.21/4.31  tff(c_84, plain, (![A_35]: (v1_funct_2(k1_xboole_0, A_35, k1_xboole_0) | k1_xboole_0=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_54])).
% 11.21/4.31  tff(c_23689, plain, (![A_35]: (v1_funct_2('#skF_3', A_35, '#skF_3') | A_35='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_23683, c_23683, c_84])).
% 11.21/4.31  tff(c_25516, plain, (![A_1799]: (v1_funct_2('#skF_1', A_1799, '#skF_1') | A_1799='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25267, c_25267, c_25267, c_23689])).
% 11.21/4.31  tff(c_23690, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23683, c_23683, c_12])).
% 11.21/4.31  tff(c_25317, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25267, c_25267, c_23690])).
% 11.21/4.31  tff(c_25276, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_25267, c_14121])).
% 11.21/4.31  tff(c_25452, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25317, c_25276])).
% 11.21/4.31  tff(c_25456, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_25452, c_18])).
% 11.21/4.31  tff(c_25402, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25267, c_25267, c_23686])).
% 11.21/4.31  tff(c_25467, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_25456, c_25402])).
% 11.21/4.31  tff(c_25277, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25267, c_14120])).
% 11.21/4.31  tff(c_25473, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25467, c_25277])).
% 11.21/4.31  tff(c_25519, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_25516, c_25473])).
% 11.21/4.31  tff(c_25523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25288, c_25519])).
% 11.21/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/4.31  
% 11.21/4.31  Inference rules
% 11.21/4.31  ----------------------
% 11.21/4.31  #Ref     : 0
% 11.21/4.31  #Sup     : 5403
% 11.21/4.31  #Fact    : 0
% 11.21/4.31  #Define  : 0
% 11.21/4.31  #Split   : 71
% 11.21/4.31  #Chain   : 0
% 11.21/4.31  #Close   : 0
% 11.21/4.31  
% 11.21/4.31  Ordering : KBO
% 11.21/4.31  
% 11.21/4.31  Simplification rules
% 11.21/4.31  ----------------------
% 11.21/4.31  #Subsume      : 720
% 11.21/4.31  #Demod        : 7487
% 11.21/4.31  #Tautology    : 2795
% 11.21/4.31  #SimpNegUnit  : 53
% 11.21/4.31  #BackRed      : 886
% 11.21/4.31  
% 11.21/4.31  #Partial instantiations: 0
% 11.21/4.31  #Strategies tried      : 1
% 11.21/4.31  
% 11.21/4.31  Timing (in seconds)
% 11.21/4.31  ----------------------
% 11.21/4.31  Preprocessing        : 0.36
% 11.21/4.31  Parsing              : 0.19
% 11.21/4.31  CNF conversion       : 0.02
% 11.21/4.31  Main loop            : 3.10
% 11.21/4.31  Inferencing          : 0.96
% 11.21/4.31  Reduction            : 1.18
% 11.21/4.31  Demodulation         : 0.86
% 11.21/4.31  BG Simplification    : 0.10
% 11.21/4.31  Subsumption          : 0.63
% 11.21/4.31  Abstraction          : 0.11
% 11.21/4.31  MUC search           : 0.00
% 11.21/4.31  Cooper               : 0.00
% 11.21/4.31  Total                : 3.61
% 11.21/4.31  Index Insertion      : 0.00
% 11.21/4.31  Index Deletion       : 0.00
% 11.21/4.31  Index Matching       : 0.00
% 11.21/4.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
