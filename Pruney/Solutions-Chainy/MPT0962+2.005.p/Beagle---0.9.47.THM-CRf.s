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
% DateTime   : Thu Dec  3 10:10:52 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 385 expanded)
%              Number of leaves         :   40 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 922 expanded)
%              Number of equality atoms :   80 ( 272 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_138,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_82,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_12,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8128,plain,(
    ! [C_1757,A_1758,B_1759] :
      ( m1_subset_1(C_1757,k1_zfmisc_1(k2_zfmisc_1(A_1758,B_1759)))
      | ~ r1_tarski(k2_relat_1(C_1757),B_1759)
      | ~ r1_tarski(k1_relat_1(C_1757),A_1758)
      | ~ v1_relat_1(C_1757) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6563,plain,(
    ! [A_1637,C_1638,B_1639] :
      ( r1_tarski(A_1637,k2_xboole_0(C_1638,B_1639))
      | ~ r1_tarski(A_1637,B_1639) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6602,plain,(
    ! [A_1641,A_1642] :
      ( r1_tarski(A_1641,A_1642)
      | ~ r1_tarski(A_1641,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_6563])).

tff(c_6615,plain,(
    ! [A_1642] : r1_tarski(k1_xboole_0,A_1642) ),
    inference(resolution,[status(thm)],[c_12,c_6602])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_84,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76])).

tff(c_176,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,(
    ! [A_34,B_35] : m1_subset_1('#skF_2'(A_34,B_35),k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_697,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_714,plain,(
    ! [A_34,B_35] : k1_relset_1(A_34,B_35,'#skF_2'(A_34,B_35)) = k1_relat_1('#skF_2'(A_34,B_35)) ),
    inference(resolution,[status(thm)],[c_74,c_697])).

tff(c_64,plain,(
    ! [A_34,B_35] : v1_funct_2('#skF_2'(A_34,B_35),A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1631,plain,(
    ! [B_172,A_173,C_174] :
      ( k1_xboole_0 = B_172
      | k1_relset_1(A_173,B_172,C_174) = A_173
      | ~ v1_funct_2(C_174,A_173,B_172)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1643,plain,(
    ! [B_35,A_34] :
      ( k1_xboole_0 = B_35
      | k1_relset_1(A_34,B_35,'#skF_2'(A_34,B_35)) = A_34
      | ~ v1_funct_2('#skF_2'(A_34,B_35),A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_74,c_1631])).

tff(c_1660,plain,(
    ! [B_35,A_34] :
      ( k1_xboole_0 = B_35
      | k1_relset_1(A_34,B_35,'#skF_2'(A_34,B_35)) = A_34 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1643])).

tff(c_2769,plain,(
    ! [B_35,A_34] :
      ( k1_xboole_0 = B_35
      | k1_relat_1('#skF_2'(A_34,B_35)) = A_34 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_1660])).

tff(c_377,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,k2_xboole_0(C_87,B_88))
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_381,plain,(
    ! [A_89,A_90] :
      ( r1_tarski(A_89,A_90)
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_377])).

tff(c_394,plain,(
    ! [A_90] : r1_tarski(k1_xboole_0,A_90) ),
    inference(resolution,[status(thm)],[c_12,c_381])).

tff(c_72,plain,(
    ! [A_34,B_35] : v1_relat_1('#skF_2'(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_563,plain,(
    ! [A_102] :
      ( k2_relat_1(A_102) = k1_xboole_0
      | k1_relat_1(A_102) != k1_xboole_0
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2175,plain,(
    ! [A_220,B_221] :
      ( k2_relat_1('#skF_2'(A_220,B_221)) = k1_xboole_0
      | k1_relat_1('#skF_2'(A_220,B_221)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_563])).

tff(c_36,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,k2_zfmisc_1(k1_relat_1(A_21),k2_relat_1(A_21)))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2181,plain,(
    ! [A_220,B_221] :
      ( r1_tarski('#skF_2'(A_220,B_221),k2_zfmisc_1(k1_relat_1('#skF_2'(A_220,B_221)),k1_xboole_0))
      | ~ v1_relat_1('#skF_2'(A_220,B_221))
      | k1_relat_1('#skF_2'(A_220,B_221)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2175,c_36])).

tff(c_3325,plain,(
    ! [A_286,B_287] :
      ( r1_tarski('#skF_2'(A_286,B_287),k1_xboole_0)
      | k1_relat_1('#skF_2'(A_286,B_287)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_22,c_2181])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3337,plain,(
    ! [A_286,B_287] :
      ( '#skF_2'(A_286,B_287) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,'#skF_2'(A_286,B_287))
      | k1_relat_1('#skF_2'(A_286,B_287)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3325,c_8])).

tff(c_3456,plain,(
    ! [A_293,B_294] :
      ( '#skF_2'(A_293,B_294) = k1_xboole_0
      | k1_relat_1('#skF_2'(A_293,B_294)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_3337])).

tff(c_3490,plain,(
    ! [A_295,B_296] :
      ( '#skF_2'(A_295,B_296) = k1_xboole_0
      | k1_xboole_0 != A_295
      | k1_xboole_0 = B_296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2769,c_3456])).

tff(c_2795,plain,(
    ! [B_262,A_263] :
      ( k1_xboole_0 = B_262
      | k1_relat_1('#skF_2'(A_263,B_262)) = A_263 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_1660])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_xboole_0(k1_relat_1(A_20))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2849,plain,(
    ! [A_263,B_262] :
      ( v1_xboole_0(A_263)
      | ~ v1_xboole_0('#skF_2'(A_263,B_262))
      | k1_xboole_0 = B_262 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2795,c_34])).

tff(c_3519,plain,(
    ! [A_295,B_296] :
      ( v1_xboole_0(A_295)
      | ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = B_296
      | k1_xboole_0 != A_295
      | k1_xboole_0 = B_296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3490,c_2849])).

tff(c_3623,plain,(
    ! [A_295,B_296] :
      ( v1_xboole_0(A_295)
      | k1_xboole_0 != A_295
      | k1_xboole_0 = B_296 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3519])).

tff(c_3662,plain,(
    ! [B_299] : k1_xboole_0 = B_299 ),
    inference(splitLeft,[status(thm)],[c_3623])).

tff(c_311,plain,(
    ! [A_76] :
      ( k1_relat_1(A_76) = k1_xboole_0
      | k2_relat_1(A_76) != k1_xboole_0
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_332,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_311])).

tff(c_367,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_578,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_563])).

tff(c_587,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_578])).

tff(c_4060,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3662,c_587])).

tff(c_4064,plain,(
    ! [A_1557] :
      ( v1_xboole_0(A_1557)
      | k1_xboole_0 != A_1557 ) ),
    inference(splitRight,[status(thm)],[c_3623])).

tff(c_6,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_594,plain,(
    ! [C_103,B_104,A_105] :
      ( ~ v1_xboole_0(C_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_103))
      | ~ r2_hidden(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1056,plain,(
    ! [B_134,A_135,A_136] :
      ( ~ v1_xboole_0(B_134)
      | ~ r2_hidden(A_135,A_136)
      | ~ r1_tarski(A_136,B_134) ) ),
    inference(resolution,[status(thm)],[c_28,c_594])).

tff(c_1060,plain,(
    ! [B_137,A_138] :
      ( ~ v1_xboole_0(B_137)
      | ~ r1_tarski(A_138,B_137)
      | k1_xboole_0 = A_138 ) ),
    inference(resolution,[status(thm)],[c_6,c_1056])).

tff(c_1084,plain,
    ( ~ v1_xboole_0('#skF_3')
    | k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_1060])).

tff(c_1098,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_1084])).

tff(c_4158,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4064,c_1098])).

tff(c_928,plain,(
    ! [C_122,A_123,B_124] :
      ( m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ r1_tarski(k2_relat_1(C_122),B_124)
      | ~ r1_tarski(k1_relat_1(C_122),A_123)
      | ~ v1_relat_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5323,plain,(
    ! [C_1591,A_1592,B_1593] :
      ( r1_tarski(C_1591,k2_zfmisc_1(A_1592,B_1593))
      | ~ r1_tarski(k2_relat_1(C_1591),B_1593)
      | ~ r1_tarski(k1_relat_1(C_1591),A_1592)
      | ~ v1_relat_1(C_1591) ) ),
    inference(resolution,[status(thm)],[c_928,c_26])).

tff(c_5337,plain,(
    ! [A_1592] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1592,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1592)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_5323])).

tff(c_5463,plain,(
    ! [A_1598] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1598,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5337])).

tff(c_5488,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_5463])).

tff(c_717,plain,(
    ! [A_112,B_113,A_14] :
      ( k1_relset_1(A_112,B_113,A_14) = k1_relat_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_28,c_697])).

tff(c_5506,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5488,c_717])).

tff(c_1378,plain,(
    ! [B_156,C_157,A_158] :
      ( k1_xboole_0 = B_156
      | v1_funct_2(C_157,A_158,B_156)
      | k1_relset_1(A_158,B_156,C_157) != A_158
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6217,plain,(
    ! [B_1618,A_1619,A_1620] :
      ( k1_xboole_0 = B_1618
      | v1_funct_2(A_1619,A_1620,B_1618)
      | k1_relset_1(A_1620,B_1618,A_1619) != A_1620
      | ~ r1_tarski(A_1619,k2_zfmisc_1(A_1620,B_1618)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1378])).

tff(c_6231,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5488,c_6217])).

tff(c_6303,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_6231])).

tff(c_6305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_4158,c_6303])).

tff(c_6306,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_6307,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_6673,plain,(
    ! [A_1649] :
      ( r1_tarski(A_1649,k2_zfmisc_1(k1_relat_1(A_1649),k2_relat_1(A_1649)))
      | ~ v1_relat_1(A_1649) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6684,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),k1_xboole_0))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6307,c_6673])).

tff(c_6705,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24,c_6306,c_6684])).

tff(c_6719,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_6705,c_8])).

tff(c_6724,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6719])).

tff(c_295,plain,(
    ! [A_74,B_75] : m1_subset_1('#skF_2'(A_74,B_75),k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_350,plain,(
    ! [B_80] : m1_subset_1('#skF_2'(k1_xboole_0,B_80),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_295])).

tff(c_354,plain,(
    ! [B_80] : r1_tarski('#skF_2'(k1_xboole_0,B_80),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_350,c_26])).

tff(c_6613,plain,(
    ! [B_80,A_1642] : r1_tarski('#skF_2'(k1_xboole_0,B_80),A_1642) ),
    inference(resolution,[status(thm)],[c_354,c_6602])).

tff(c_6617,plain,(
    ! [A_1643] : r1_tarski(k1_xboole_0,A_1643) ),
    inference(resolution,[status(thm)],[c_12,c_6602])).

tff(c_6646,plain,(
    ! [A_1648] :
      ( k1_xboole_0 = A_1648
      | ~ r1_tarski(A_1648,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6617,c_8])).

tff(c_6667,plain,(
    ! [B_80] : '#skF_2'(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6613,c_6646])).

tff(c_7067,plain,(
    ! [B_1666] : '#skF_2'('#skF_4',B_1666) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6724,c_6724,c_6667])).

tff(c_7081,plain,(
    ! [B_1666] : v1_funct_2('#skF_4','#skF_4',B_1666) ),
    inference(superposition,[status(thm),theory(equality)],[c_7067,c_64])).

tff(c_6308,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6306,c_176])).

tff(c_6740,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6724,c_6308])).

tff(c_7112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7081,c_6740])).

tff(c_7113,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_8139,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8128,c_7113])).

tff(c_8155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12,c_78,c_8139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.46  
% 7.21/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 7.21/2.46  
% 7.21/2.46  %Foreground sorts:
% 7.21/2.46  
% 7.21/2.46  
% 7.21/2.46  %Background operators:
% 7.21/2.46  
% 7.21/2.46  
% 7.21/2.46  %Foreground operators:
% 7.21/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.21/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.21/2.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.21/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.21/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.21/2.46  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.21/2.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.21/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.21/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.21/2.46  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.21/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.21/2.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.21/2.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.21/2.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.21/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.21/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.46  
% 7.21/2.48  tff(f_151, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 7.21/2.48  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.21/2.48  tff(f_105, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.21/2.48  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.21/2.48  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.21/2.48  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.21/2.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.21/2.48  tff(f_138, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 7.21/2.48  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.21/2.48  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.21/2.48  tff(f_89, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 7.21/2.48  tff(f_83, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 7.21/2.48  tff(f_79, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 7.21/2.48  tff(f_38, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.21/2.48  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.21/2.48  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.21/2.48  tff(c_82, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.48  tff(c_12, plain, (![B_5]: (r1_tarski(B_5, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.21/2.48  tff(c_78, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.48  tff(c_8128, plain, (![C_1757, A_1758, B_1759]: (m1_subset_1(C_1757, k1_zfmisc_1(k2_zfmisc_1(A_1758, B_1759))) | ~r1_tarski(k2_relat_1(C_1757), B_1759) | ~r1_tarski(k1_relat_1(C_1757), A_1758) | ~v1_relat_1(C_1757))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.48  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.21/2.48  tff(c_6563, plain, (![A_1637, C_1638, B_1639]: (r1_tarski(A_1637, k2_xboole_0(C_1638, B_1639)) | ~r1_tarski(A_1637, B_1639))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.21/2.48  tff(c_6602, plain, (![A_1641, A_1642]: (r1_tarski(A_1641, A_1642) | ~r1_tarski(A_1641, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_6563])).
% 7.21/2.48  tff(c_6615, plain, (![A_1642]: (r1_tarski(k1_xboole_0, A_1642))), inference(resolution, [status(thm)], [c_12, c_6602])).
% 7.21/2.48  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.48  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.48  tff(c_76, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.21/2.48  tff(c_84, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76])).
% 7.21/2.48  tff(c_176, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 7.21/2.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.21/2.48  tff(c_74, plain, (![A_34, B_35]: (m1_subset_1('#skF_2'(A_34, B_35), k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.21/2.48  tff(c_697, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.21/2.48  tff(c_714, plain, (![A_34, B_35]: (k1_relset_1(A_34, B_35, '#skF_2'(A_34, B_35))=k1_relat_1('#skF_2'(A_34, B_35)))), inference(resolution, [status(thm)], [c_74, c_697])).
% 7.21/2.48  tff(c_64, plain, (![A_34, B_35]: (v1_funct_2('#skF_2'(A_34, B_35), A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.21/2.48  tff(c_1631, plain, (![B_172, A_173, C_174]: (k1_xboole_0=B_172 | k1_relset_1(A_173, B_172, C_174)=A_173 | ~v1_funct_2(C_174, A_173, B_172) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.21/2.48  tff(c_1643, plain, (![B_35, A_34]: (k1_xboole_0=B_35 | k1_relset_1(A_34, B_35, '#skF_2'(A_34, B_35))=A_34 | ~v1_funct_2('#skF_2'(A_34, B_35), A_34, B_35))), inference(resolution, [status(thm)], [c_74, c_1631])).
% 7.21/2.48  tff(c_1660, plain, (![B_35, A_34]: (k1_xboole_0=B_35 | k1_relset_1(A_34, B_35, '#skF_2'(A_34, B_35))=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1643])).
% 7.21/2.48  tff(c_2769, plain, (![B_35, A_34]: (k1_xboole_0=B_35 | k1_relat_1('#skF_2'(A_34, B_35))=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_714, c_1660])).
% 7.21/2.48  tff(c_377, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, k2_xboole_0(C_87, B_88)) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.21/2.48  tff(c_381, plain, (![A_89, A_90]: (r1_tarski(A_89, A_90) | ~r1_tarski(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_377])).
% 7.21/2.48  tff(c_394, plain, (![A_90]: (r1_tarski(k1_xboole_0, A_90))), inference(resolution, [status(thm)], [c_12, c_381])).
% 7.21/2.48  tff(c_72, plain, (![A_34, B_35]: (v1_relat_1('#skF_2'(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.21/2.48  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.48  tff(c_563, plain, (![A_102]: (k2_relat_1(A_102)=k1_xboole_0 | k1_relat_1(A_102)!=k1_xboole_0 | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.21/2.48  tff(c_2175, plain, (![A_220, B_221]: (k2_relat_1('#skF_2'(A_220, B_221))=k1_xboole_0 | k1_relat_1('#skF_2'(A_220, B_221))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_563])).
% 7.21/2.48  tff(c_36, plain, (![A_21]: (r1_tarski(A_21, k2_zfmisc_1(k1_relat_1(A_21), k2_relat_1(A_21))) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.21/2.48  tff(c_2181, plain, (![A_220, B_221]: (r1_tarski('#skF_2'(A_220, B_221), k2_zfmisc_1(k1_relat_1('#skF_2'(A_220, B_221)), k1_xboole_0)) | ~v1_relat_1('#skF_2'(A_220, B_221)) | k1_relat_1('#skF_2'(A_220, B_221))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2175, c_36])).
% 7.21/2.48  tff(c_3325, plain, (![A_286, B_287]: (r1_tarski('#skF_2'(A_286, B_287), k1_xboole_0) | k1_relat_1('#skF_2'(A_286, B_287))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_22, c_2181])).
% 7.21/2.48  tff(c_8, plain, (![B_5, A_4]: (B_5=A_4 | ~r1_tarski(B_5, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.21/2.48  tff(c_3337, plain, (![A_286, B_287]: ('#skF_2'(A_286, B_287)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_2'(A_286, B_287)) | k1_relat_1('#skF_2'(A_286, B_287))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3325, c_8])).
% 7.21/2.48  tff(c_3456, plain, (![A_293, B_294]: ('#skF_2'(A_293, B_294)=k1_xboole_0 | k1_relat_1('#skF_2'(A_293, B_294))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_3337])).
% 7.21/2.48  tff(c_3490, plain, (![A_295, B_296]: ('#skF_2'(A_295, B_296)=k1_xboole_0 | k1_xboole_0!=A_295 | k1_xboole_0=B_296)), inference(superposition, [status(thm), theory('equality')], [c_2769, c_3456])).
% 7.21/2.48  tff(c_2795, plain, (![B_262, A_263]: (k1_xboole_0=B_262 | k1_relat_1('#skF_2'(A_263, B_262))=A_263)), inference(demodulation, [status(thm), theory('equality')], [c_714, c_1660])).
% 7.21/2.48  tff(c_34, plain, (![A_20]: (v1_xboole_0(k1_relat_1(A_20)) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.21/2.48  tff(c_2849, plain, (![A_263, B_262]: (v1_xboole_0(A_263) | ~v1_xboole_0('#skF_2'(A_263, B_262)) | k1_xboole_0=B_262)), inference(superposition, [status(thm), theory('equality')], [c_2795, c_34])).
% 7.21/2.48  tff(c_3519, plain, (![A_295, B_296]: (v1_xboole_0(A_295) | ~v1_xboole_0(k1_xboole_0) | k1_xboole_0=B_296 | k1_xboole_0!=A_295 | k1_xboole_0=B_296)), inference(superposition, [status(thm), theory('equality')], [c_3490, c_2849])).
% 7.21/2.48  tff(c_3623, plain, (![A_295, B_296]: (v1_xboole_0(A_295) | k1_xboole_0!=A_295 | k1_xboole_0=B_296)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3519])).
% 7.21/2.48  tff(c_3662, plain, (![B_299]: (k1_xboole_0=B_299)), inference(splitLeft, [status(thm)], [c_3623])).
% 7.21/2.48  tff(c_311, plain, (![A_76]: (k1_relat_1(A_76)=k1_xboole_0 | k2_relat_1(A_76)!=k1_xboole_0 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.21/2.48  tff(c_332, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_311])).
% 7.21/2.48  tff(c_367, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_332])).
% 7.21/2.48  tff(c_578, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_563])).
% 7.21/2.48  tff(c_587, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_367, c_578])).
% 7.21/2.48  tff(c_4060, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3662, c_587])).
% 7.21/2.48  tff(c_4064, plain, (![A_1557]: (v1_xboole_0(A_1557) | k1_xboole_0!=A_1557)), inference(splitRight, [status(thm)], [c_3623])).
% 7.21/2.48  tff(c_6, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.21/2.48  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.21/2.48  tff(c_594, plain, (![C_103, B_104, A_105]: (~v1_xboole_0(C_103) | ~m1_subset_1(B_104, k1_zfmisc_1(C_103)) | ~r2_hidden(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.21/2.48  tff(c_1056, plain, (![B_134, A_135, A_136]: (~v1_xboole_0(B_134) | ~r2_hidden(A_135, A_136) | ~r1_tarski(A_136, B_134))), inference(resolution, [status(thm)], [c_28, c_594])).
% 7.21/2.48  tff(c_1060, plain, (![B_137, A_138]: (~v1_xboole_0(B_137) | ~r1_tarski(A_138, B_137) | k1_xboole_0=A_138)), inference(resolution, [status(thm)], [c_6, c_1056])).
% 7.21/2.48  tff(c_1084, plain, (~v1_xboole_0('#skF_3') | k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_1060])).
% 7.21/2.48  tff(c_1098, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_367, c_1084])).
% 7.21/2.48  tff(c_4158, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_4064, c_1098])).
% 7.21/2.48  tff(c_928, plain, (![C_122, A_123, B_124]: (m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~r1_tarski(k2_relat_1(C_122), B_124) | ~r1_tarski(k1_relat_1(C_122), A_123) | ~v1_relat_1(C_122))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.48  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.21/2.48  tff(c_5323, plain, (![C_1591, A_1592, B_1593]: (r1_tarski(C_1591, k2_zfmisc_1(A_1592, B_1593)) | ~r1_tarski(k2_relat_1(C_1591), B_1593) | ~r1_tarski(k1_relat_1(C_1591), A_1592) | ~v1_relat_1(C_1591))), inference(resolution, [status(thm)], [c_928, c_26])).
% 7.21/2.48  tff(c_5337, plain, (![A_1592]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1592, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_1592) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_5323])).
% 7.21/2.48  tff(c_5463, plain, (![A_1598]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1598, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_1598))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_5337])).
% 7.21/2.48  tff(c_5488, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_5463])).
% 7.21/2.48  tff(c_717, plain, (![A_112, B_113, A_14]: (k1_relset_1(A_112, B_113, A_14)=k1_relat_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_112, B_113)))), inference(resolution, [status(thm)], [c_28, c_697])).
% 7.21/2.48  tff(c_5506, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5488, c_717])).
% 7.21/2.48  tff(c_1378, plain, (![B_156, C_157, A_158]: (k1_xboole_0=B_156 | v1_funct_2(C_157, A_158, B_156) | k1_relset_1(A_158, B_156, C_157)!=A_158 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.21/2.48  tff(c_6217, plain, (![B_1618, A_1619, A_1620]: (k1_xboole_0=B_1618 | v1_funct_2(A_1619, A_1620, B_1618) | k1_relset_1(A_1620, B_1618, A_1619)!=A_1620 | ~r1_tarski(A_1619, k2_zfmisc_1(A_1620, B_1618)))), inference(resolution, [status(thm)], [c_28, c_1378])).
% 7.21/2.48  tff(c_6231, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5488, c_6217])).
% 7.21/2.48  tff(c_6303, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_6231])).
% 7.21/2.48  tff(c_6305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_4158, c_6303])).
% 7.21/2.48  tff(c_6306, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_332])).
% 7.21/2.48  tff(c_6307, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_332])).
% 7.21/2.48  tff(c_6673, plain, (![A_1649]: (r1_tarski(A_1649, k2_zfmisc_1(k1_relat_1(A_1649), k2_relat_1(A_1649))) | ~v1_relat_1(A_1649))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.21/2.48  tff(c_6684, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), k1_xboole_0)) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6307, c_6673])).
% 7.21/2.48  tff(c_6705, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24, c_6306, c_6684])).
% 7.21/2.48  tff(c_6719, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_6705, c_8])).
% 7.21/2.48  tff(c_6724, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6719])).
% 7.21/2.48  tff(c_295, plain, (![A_74, B_75]: (m1_subset_1('#skF_2'(A_74, B_75), k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.21/2.48  tff(c_350, plain, (![B_80]: (m1_subset_1('#skF_2'(k1_xboole_0, B_80), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_295])).
% 7.21/2.48  tff(c_354, plain, (![B_80]: (r1_tarski('#skF_2'(k1_xboole_0, B_80), k1_xboole_0))), inference(resolution, [status(thm)], [c_350, c_26])).
% 7.21/2.48  tff(c_6613, plain, (![B_80, A_1642]: (r1_tarski('#skF_2'(k1_xboole_0, B_80), A_1642))), inference(resolution, [status(thm)], [c_354, c_6602])).
% 7.21/2.48  tff(c_6617, plain, (![A_1643]: (r1_tarski(k1_xboole_0, A_1643))), inference(resolution, [status(thm)], [c_12, c_6602])).
% 7.21/2.48  tff(c_6646, plain, (![A_1648]: (k1_xboole_0=A_1648 | ~r1_tarski(A_1648, k1_xboole_0))), inference(resolution, [status(thm)], [c_6617, c_8])).
% 7.21/2.48  tff(c_6667, plain, (![B_80]: ('#skF_2'(k1_xboole_0, B_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6613, c_6646])).
% 7.21/2.48  tff(c_7067, plain, (![B_1666]: ('#skF_2'('#skF_4', B_1666)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6724, c_6724, c_6667])).
% 7.21/2.48  tff(c_7081, plain, (![B_1666]: (v1_funct_2('#skF_4', '#skF_4', B_1666))), inference(superposition, [status(thm), theory('equality')], [c_7067, c_64])).
% 7.21/2.48  tff(c_6308, plain, (~v1_funct_2('#skF_4', k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6306, c_176])).
% 7.21/2.48  tff(c_6740, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6724, c_6308])).
% 7.21/2.48  tff(c_7112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7081, c_6740])).
% 7.21/2.48  tff(c_7113, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_84])).
% 7.21/2.48  tff(c_8139, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8128, c_7113])).
% 7.21/2.48  tff(c_8155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_12, c_78, c_8139])).
% 7.21/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.48  
% 7.21/2.48  Inference rules
% 7.21/2.48  ----------------------
% 7.21/2.48  #Ref     : 0
% 7.21/2.48  #Sup     : 1934
% 7.21/2.48  #Fact    : 0
% 7.21/2.48  #Define  : 0
% 7.21/2.48  #Split   : 12
% 7.21/2.48  #Chain   : 0
% 7.21/2.48  #Close   : 0
% 7.21/2.48  
% 7.21/2.48  Ordering : KBO
% 7.21/2.48  
% 7.21/2.48  Simplification rules
% 7.21/2.48  ----------------------
% 7.21/2.48  #Subsume      : 427
% 7.21/2.48  #Demod        : 1385
% 7.21/2.48  #Tautology    : 911
% 7.21/2.48  #SimpNegUnit  : 9
% 7.21/2.48  #BackRed      : 53
% 7.21/2.48  
% 7.21/2.48  #Partial instantiations: 174
% 7.21/2.48  #Strategies tried      : 1
% 7.21/2.48  
% 7.21/2.48  Timing (in seconds)
% 7.21/2.48  ----------------------
% 7.21/2.48  Preprocessing        : 0.35
% 7.21/2.48  Parsing              : 0.18
% 7.21/2.48  CNF conversion       : 0.02
% 7.21/2.48  Main loop            : 1.35
% 7.21/2.48  Inferencing          : 0.46
% 7.21/2.48  Reduction            : 0.46
% 7.21/2.48  Demodulation         : 0.33
% 7.21/2.48  BG Simplification    : 0.05
% 7.21/2.48  Subsumption          : 0.28
% 7.21/2.48  Abstraction          : 0.06
% 7.21/2.48  MUC search           : 0.00
% 7.21/2.48  Cooper               : 0.00
% 7.21/2.48  Total                : 1.75
% 7.21/2.48  Index Insertion      : 0.00
% 7.21/2.48  Index Deletion       : 0.00
% 7.21/2.48  Index Matching       : 0.00
% 7.21/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
