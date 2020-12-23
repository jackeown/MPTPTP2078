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
% DateTime   : Thu Dec  3 10:08:14 EST 2020

% Result     : Theorem 5.14s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 295 expanded)
%              Number of leaves         :   46 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  204 ( 602 expanded)
%              Number of equality atoms :   78 ( 142 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2772,plain,(
    ! [A_405,B_406,C_407] :
      ( k1_relset_1(A_405,B_406,C_407) = k1_relat_1(C_407)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2786,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2772])).

tff(c_52,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2795,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2786,c_52])).

tff(c_30,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_130,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_124])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_130])).

tff(c_841,plain,(
    ! [A_181,B_182,C_183] :
      ( k1_relset_1(A_181,B_182,C_183) = k1_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_855,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_841])).

tff(c_861,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_52])).

tff(c_196,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_205,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_196])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_760,plain,(
    ! [A_177,B_178,C_179] :
      ( k2_relset_1(A_177,B_178,C_179) = k2_relat_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_774,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_760])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_338,plain,(
    ! [A_109,C_110,B_111] :
      ( m1_subset_1(A_109,C_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(C_110))
      | ~ r2_hidden(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_366,plain,(
    ! [A_115,B_116,A_117] :
      ( m1_subset_1(A_115,B_116)
      | ~ r2_hidden(A_115,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(resolution,[status(thm)],[c_20,c_338])).

tff(c_390,plain,(
    ! [A_123,B_124] :
      ( m1_subset_1('#skF_1'(A_123),B_124)
      | ~ r1_tarski(A_123,B_124)
      | k1_xboole_0 = A_123 ) ),
    inference(resolution,[status(thm)],[c_2,c_366])).

tff(c_71,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_60,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_135,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_416,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_390,c_135])).

tff(c_503,plain,(
    ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_776,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_503])).

tff(c_785,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_776])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_205,c_785])).

tff(c_793,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_875,plain,(
    ! [A_186,B_187,C_188] :
      ( k2_relset_1(A_186,B_187,C_188) = k2_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_886,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_875])).

tff(c_890,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_886])).

tff(c_16,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_440,plain,(
    ! [A_130,B_131] :
      ( k8_relat_1(A_130,B_131) = B_131
      | ~ r1_tarski(k2_relat_1(B_131),A_130)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_482,plain,(
    ! [A_135,B_136] :
      ( k8_relat_1(A_135,B_136) = B_136
      | ~ v5_relat_1(B_136,A_135)
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_28,c_440])).

tff(c_491,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_482])).

tff(c_498,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_491])).

tff(c_458,plain,(
    ! [B_132,A_133] :
      ( k3_xboole_0(B_132,k2_zfmisc_1(k1_relat_1(B_132),A_133)) = k8_relat_1(A_133,B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1623,plain,(
    ! [B_267,A_268] :
      ( k4_xboole_0(B_267,k2_zfmisc_1(k1_relat_1(B_267),A_268)) = k5_xboole_0(B_267,k8_relat_1(A_268,B_267))
      | ~ v1_relat_1(B_267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_14])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_262,plain,(
    ! [C_99,A_100,B_101] :
      ( v4_relat_1(C_99,A_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_296,plain,(
    ! [A_102,A_103,B_104] :
      ( v4_relat_1(A_102,A_103)
      | ~ r1_tarski(A_102,k2_zfmisc_1(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_20,c_262])).

tff(c_315,plain,(
    ! [A_5,A_103,B_104] :
      ( v4_relat_1(A_5,A_103)
      | k4_xboole_0(A_5,k2_zfmisc_1(A_103,B_104)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_296])).

tff(c_2099,plain,(
    ! [B_321,A_322] :
      ( v4_relat_1(B_321,k1_relat_1(B_321))
      | k5_xboole_0(B_321,k8_relat_1(A_322,B_321)) != k1_xboole_0
      | ~ v1_relat_1(B_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1623,c_315])).

tff(c_2107,plain,
    ( v4_relat_1('#skF_4',k1_relat_1('#skF_4'))
    | k5_xboole_0('#skF_4','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_2099])).

tff(c_2117,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_16,c_2107])).

tff(c_40,plain,(
    ! [B_31,A_30] :
      ( k7_relat_1(B_31,A_30) = B_31
      | ~ v4_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2166,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2117,c_40])).

tff(c_2169,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2166])).

tff(c_36,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2180,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2169,c_36])).

tff(c_2188,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_890,c_2180])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_982,plain,(
    ! [B_192,A_193] :
      ( k9_relat_1(B_192,A_193) != k1_xboole_0
      | ~ r1_tarski(A_193,k1_relat_1(B_192))
      | k1_xboole_0 = A_193
      | ~ v1_relat_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_997,plain,(
    ! [B_192] :
      ( k9_relat_1(B_192,k1_relat_1(B_192)) != k1_xboole_0
      | k1_relat_1(B_192) = k1_xboole_0
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_8,c_982])).

tff(c_2213,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2188,c_997])).

tff(c_2221,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2213])).

tff(c_2223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_2221])).

tff(c_2224,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2664,plain,(
    ! [A_401,B_402,C_403] :
      ( k2_relset_1(A_401,B_402,C_403) = k2_relat_1(C_403)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2675,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_2664])).

tff(c_2679,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_2675])).

tff(c_2505,plain,(
    ! [A_384,B_385] :
      ( k8_relat_1(A_384,B_385) = B_385
      | ~ r1_tarski(k2_relat_1(B_385),A_384)
      | ~ v1_relat_1(B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2522,plain,(
    ! [B_385] :
      ( k8_relat_1(k2_relat_1(B_385),B_385) = B_385
      | ~ v1_relat_1(B_385) ) ),
    inference(resolution,[status(thm)],[c_8,c_2505])).

tff(c_2690,plain,
    ( k8_relat_1(k1_xboole_0,'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2679,c_2522])).

tff(c_2710,plain,(
    k8_relat_1(k1_xboole_0,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2690])).

tff(c_2556,plain,(
    ! [B_389,A_390] :
      ( k3_xboole_0(B_389,k2_zfmisc_1(k1_relat_1(B_389),A_390)) = k8_relat_1(A_390,B_389)
      | ~ v1_relat_1(B_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3609,plain,(
    ! [B_513,A_514] :
      ( k4_xboole_0(B_513,k2_zfmisc_1(k1_relat_1(B_513),A_514)) = k5_xboole_0(B_513,k8_relat_1(A_514,B_513))
      | ~ v1_relat_1(B_513) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2556,c_14])).

tff(c_2353,plain,(
    ! [C_355,A_356,B_357] :
      ( v4_relat_1(C_355,A_356)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2363,plain,(
    ! [A_358,A_359,B_360] :
      ( v4_relat_1(A_358,A_359)
      | ~ r1_tarski(A_358,k2_zfmisc_1(A_359,B_360)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2353])).

tff(c_2377,plain,(
    ! [A_5,A_359,B_360] :
      ( v4_relat_1(A_5,A_359)
      | k4_xboole_0(A_5,k2_zfmisc_1(A_359,B_360)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_2363])).

tff(c_3725,plain,(
    ! [B_522,A_523] :
      ( v4_relat_1(B_522,k1_relat_1(B_522))
      | k5_xboole_0(B_522,k8_relat_1(A_523,B_522)) != k1_xboole_0
      | ~ v1_relat_1(B_522) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3609,c_2377])).

tff(c_3729,plain,
    ( v4_relat_1('#skF_4',k1_relat_1('#skF_4'))
    | k5_xboole_0('#skF_4','#skF_4') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2710,c_3725])).

tff(c_3739,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_16,c_3729])).

tff(c_3748,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3739,c_40])).

tff(c_3751,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_3748])).

tff(c_3756,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3751,c_36])).

tff(c_3760,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2679,c_3756])).

tff(c_2815,plain,(
    ! [B_409,A_410] :
      ( k9_relat_1(B_409,A_410) != k1_xboole_0
      | ~ r1_tarski(A_410,k1_relat_1(B_409))
      | k1_xboole_0 = A_410
      | ~ v1_relat_1(B_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2830,plain,(
    ! [B_409] :
      ( k9_relat_1(B_409,k1_relat_1(B_409)) != k1_xboole_0
      | k1_relat_1(B_409) = k1_xboole_0
      | ~ v1_relat_1(B_409) ) ),
    inference(resolution,[status(thm)],[c_8,c_2815])).

tff(c_3805,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3760,c_2830])).

tff(c_3810,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_3805])).

tff(c_3812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2795,c_3810])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.14/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.97  
% 5.14/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.97  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 5.14/1.97  
% 5.14/1.97  %Foreground sorts:
% 5.14/1.97  
% 5.14/1.97  
% 5.14/1.97  %Background operators:
% 5.14/1.97  
% 5.14/1.97  
% 5.14/1.97  %Foreground operators:
% 5.14/1.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.14/1.97  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 5.14/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.14/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.14/1.97  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.14/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.14/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.14/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/1.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.14/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.14/1.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.14/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.14/1.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.14/1.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.14/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.14/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.14/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.14/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/1.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.14/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.14/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.14/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.14/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.14/1.97  
% 5.14/1.99  tff(f_137, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 5.14/1.99  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.14/1.99  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.14/1.99  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.14/1.99  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.14/1.99  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.14/1.99  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.14/1.99  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.14/1.99  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.14/1.99  tff(f_57, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.14/1.99  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.14/1.99  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 5.14/1.99  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 5.14/1.99  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.14/1.99  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.14/1.99  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.14/1.99  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.14/1.99  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/1.99  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 5.14/1.99  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.14/1.99  tff(c_2772, plain, (![A_405, B_406, C_407]: (k1_relset_1(A_405, B_406, C_407)=k1_relat_1(C_407) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.14/1.99  tff(c_2786, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2772])).
% 5.14/1.99  tff(c_52, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.14/1.99  tff(c_2795, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2786, c_52])).
% 5.14/1.99  tff(c_30, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.14/1.99  tff(c_124, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.14/1.99  tff(c_130, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_124])).
% 5.14/1.99  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_130])).
% 5.14/1.99  tff(c_841, plain, (![A_181, B_182, C_183]: (k1_relset_1(A_181, B_182, C_183)=k1_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.14/1.99  tff(c_855, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_841])).
% 5.14/1.99  tff(c_861, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_855, c_52])).
% 5.14/1.99  tff(c_196, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.14/1.99  tff(c_205, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_196])).
% 5.14/1.99  tff(c_28, plain, (![B_19, A_18]: (r1_tarski(k2_relat_1(B_19), A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.14/1.99  tff(c_760, plain, (![A_177, B_178, C_179]: (k2_relset_1(A_177, B_178, C_179)=k2_relat_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.14/1.99  tff(c_774, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_760])).
% 5.14/1.99  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.14/1.99  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.14/1.99  tff(c_338, plain, (![A_109, C_110, B_111]: (m1_subset_1(A_109, C_110) | ~m1_subset_1(B_111, k1_zfmisc_1(C_110)) | ~r2_hidden(A_109, B_111))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.14/1.99  tff(c_366, plain, (![A_115, B_116, A_117]: (m1_subset_1(A_115, B_116) | ~r2_hidden(A_115, A_117) | ~r1_tarski(A_117, B_116))), inference(resolution, [status(thm)], [c_20, c_338])).
% 5.14/1.99  tff(c_390, plain, (![A_123, B_124]: (m1_subset_1('#skF_1'(A_123), B_124) | ~r1_tarski(A_123, B_124) | k1_xboole_0=A_123)), inference(resolution, [status(thm)], [c_2, c_366])).
% 5.14/1.99  tff(c_71, plain, (![D_60]: (~r2_hidden(D_60, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_60, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.14/1.99  tff(c_76, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_71])).
% 5.14/1.99  tff(c_135, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 5.14/1.99  tff(c_416, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_390, c_135])).
% 5.14/1.99  tff(c_503, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_416])).
% 5.14/1.99  tff(c_776, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_774, c_503])).
% 5.14/1.99  tff(c_785, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_776])).
% 5.14/1.99  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_205, c_785])).
% 5.14/1.99  tff(c_793, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_416])).
% 5.14/1.99  tff(c_875, plain, (![A_186, B_187, C_188]: (k2_relset_1(A_186, B_187, C_188)=k2_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.14/1.99  tff(c_886, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_875])).
% 5.14/1.99  tff(c_890, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_793, c_886])).
% 5.14/1.99  tff(c_16, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.14/1.99  tff(c_440, plain, (![A_130, B_131]: (k8_relat_1(A_130, B_131)=B_131 | ~r1_tarski(k2_relat_1(B_131), A_130) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.14/1.99  tff(c_482, plain, (![A_135, B_136]: (k8_relat_1(A_135, B_136)=B_136 | ~v5_relat_1(B_136, A_135) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_28, c_440])).
% 5.14/1.99  tff(c_491, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_205, c_482])).
% 5.14/1.99  tff(c_498, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_491])).
% 5.14/1.99  tff(c_458, plain, (![B_132, A_133]: (k3_xboole_0(B_132, k2_zfmisc_1(k1_relat_1(B_132), A_133))=k8_relat_1(A_133, B_132) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.14/1.99  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.14/1.99  tff(c_1623, plain, (![B_267, A_268]: (k4_xboole_0(B_267, k2_zfmisc_1(k1_relat_1(B_267), A_268))=k5_xboole_0(B_267, k8_relat_1(A_268, B_267)) | ~v1_relat_1(B_267))), inference(superposition, [status(thm), theory('equality')], [c_458, c_14])).
% 5.14/1.99  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.14/1.99  tff(c_262, plain, (![C_99, A_100, B_101]: (v4_relat_1(C_99, A_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.14/1.99  tff(c_296, plain, (![A_102, A_103, B_104]: (v4_relat_1(A_102, A_103) | ~r1_tarski(A_102, k2_zfmisc_1(A_103, B_104)))), inference(resolution, [status(thm)], [c_20, c_262])).
% 5.14/1.99  tff(c_315, plain, (![A_5, A_103, B_104]: (v4_relat_1(A_5, A_103) | k4_xboole_0(A_5, k2_zfmisc_1(A_103, B_104))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_296])).
% 5.14/1.99  tff(c_2099, plain, (![B_321, A_322]: (v4_relat_1(B_321, k1_relat_1(B_321)) | k5_xboole_0(B_321, k8_relat_1(A_322, B_321))!=k1_xboole_0 | ~v1_relat_1(B_321))), inference(superposition, [status(thm), theory('equality')], [c_1623, c_315])).
% 5.14/1.99  tff(c_2107, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4')) | k5_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_498, c_2099])).
% 5.14/1.99  tff(c_2117, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_16, c_2107])).
% 5.14/1.99  tff(c_40, plain, (![B_31, A_30]: (k7_relat_1(B_31, A_30)=B_31 | ~v4_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.14/1.99  tff(c_2166, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2117, c_40])).
% 5.14/1.99  tff(c_2169, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_2166])).
% 5.14/1.99  tff(c_36, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.14/1.99  tff(c_2180, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2169, c_36])).
% 5.14/1.99  tff(c_2188, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_134, c_890, c_2180])).
% 5.14/1.99  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.14/1.99  tff(c_982, plain, (![B_192, A_193]: (k9_relat_1(B_192, A_193)!=k1_xboole_0 | ~r1_tarski(A_193, k1_relat_1(B_192)) | k1_xboole_0=A_193 | ~v1_relat_1(B_192))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.14/1.99  tff(c_997, plain, (![B_192]: (k9_relat_1(B_192, k1_relat_1(B_192))!=k1_xboole_0 | k1_relat_1(B_192)=k1_xboole_0 | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_8, c_982])).
% 5.14/1.99  tff(c_2213, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2188, c_997])).
% 5.14/1.99  tff(c_2221, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_134, c_2213])).
% 5.14/1.99  tff(c_2223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_861, c_2221])).
% 5.14/1.99  tff(c_2224, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_76])).
% 5.14/1.99  tff(c_2664, plain, (![A_401, B_402, C_403]: (k2_relset_1(A_401, B_402, C_403)=k2_relat_1(C_403) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.14/1.99  tff(c_2675, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_2664])).
% 5.14/1.99  tff(c_2679, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_2675])).
% 5.14/1.99  tff(c_2505, plain, (![A_384, B_385]: (k8_relat_1(A_384, B_385)=B_385 | ~r1_tarski(k2_relat_1(B_385), A_384) | ~v1_relat_1(B_385))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.14/1.99  tff(c_2522, plain, (![B_385]: (k8_relat_1(k2_relat_1(B_385), B_385)=B_385 | ~v1_relat_1(B_385))), inference(resolution, [status(thm)], [c_8, c_2505])).
% 5.14/1.99  tff(c_2690, plain, (k8_relat_1(k1_xboole_0, '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2679, c_2522])).
% 5.14/1.99  tff(c_2710, plain, (k8_relat_1(k1_xboole_0, '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_2690])).
% 5.14/1.99  tff(c_2556, plain, (![B_389, A_390]: (k3_xboole_0(B_389, k2_zfmisc_1(k1_relat_1(B_389), A_390))=k8_relat_1(A_390, B_389) | ~v1_relat_1(B_389))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.14/1.99  tff(c_3609, plain, (![B_513, A_514]: (k4_xboole_0(B_513, k2_zfmisc_1(k1_relat_1(B_513), A_514))=k5_xboole_0(B_513, k8_relat_1(A_514, B_513)) | ~v1_relat_1(B_513))), inference(superposition, [status(thm), theory('equality')], [c_2556, c_14])).
% 5.14/1.99  tff(c_2353, plain, (![C_355, A_356, B_357]: (v4_relat_1(C_355, A_356) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.14/1.99  tff(c_2363, plain, (![A_358, A_359, B_360]: (v4_relat_1(A_358, A_359) | ~r1_tarski(A_358, k2_zfmisc_1(A_359, B_360)))), inference(resolution, [status(thm)], [c_20, c_2353])).
% 5.14/1.99  tff(c_2377, plain, (![A_5, A_359, B_360]: (v4_relat_1(A_5, A_359) | k4_xboole_0(A_5, k2_zfmisc_1(A_359, B_360))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2363])).
% 5.14/1.99  tff(c_3725, plain, (![B_522, A_523]: (v4_relat_1(B_522, k1_relat_1(B_522)) | k5_xboole_0(B_522, k8_relat_1(A_523, B_522))!=k1_xboole_0 | ~v1_relat_1(B_522))), inference(superposition, [status(thm), theory('equality')], [c_3609, c_2377])).
% 5.14/1.99  tff(c_3729, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4')) | k5_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2710, c_3725])).
% 5.14/1.99  tff(c_3739, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_16, c_3729])).
% 5.14/1.99  tff(c_3748, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3739, c_40])).
% 5.14/1.99  tff(c_3751, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_3748])).
% 5.14/1.99  tff(c_3756, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3751, c_36])).
% 5.14/1.99  tff(c_3760, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_134, c_2679, c_3756])).
% 5.14/1.99  tff(c_2815, plain, (![B_409, A_410]: (k9_relat_1(B_409, A_410)!=k1_xboole_0 | ~r1_tarski(A_410, k1_relat_1(B_409)) | k1_xboole_0=A_410 | ~v1_relat_1(B_409))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.14/1.99  tff(c_2830, plain, (![B_409]: (k9_relat_1(B_409, k1_relat_1(B_409))!=k1_xboole_0 | k1_relat_1(B_409)=k1_xboole_0 | ~v1_relat_1(B_409))), inference(resolution, [status(thm)], [c_8, c_2815])).
% 5.14/1.99  tff(c_3805, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3760, c_2830])).
% 5.14/1.99  tff(c_3810, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_134, c_3805])).
% 5.14/1.99  tff(c_3812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2795, c_3810])).
% 5.14/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.99  
% 5.14/1.99  Inference rules
% 5.14/1.99  ----------------------
% 5.14/1.99  #Ref     : 0
% 5.14/1.99  #Sup     : 782
% 5.14/1.99  #Fact    : 0
% 5.14/1.99  #Define  : 0
% 5.14/1.99  #Split   : 17
% 5.14/1.99  #Chain   : 0
% 5.14/1.99  #Close   : 0
% 5.14/1.99  
% 5.14/1.99  Ordering : KBO
% 5.14/1.99  
% 5.14/1.99  Simplification rules
% 5.14/1.99  ----------------------
% 5.14/1.99  #Subsume      : 103
% 5.14/1.99  #Demod        : 373
% 5.14/1.99  #Tautology    : 226
% 5.14/1.99  #SimpNegUnit  : 5
% 5.14/1.99  #BackRed      : 12
% 5.14/1.99  
% 5.14/1.99  #Partial instantiations: 0
% 5.14/1.99  #Strategies tried      : 1
% 5.14/1.99  
% 5.14/1.99  Timing (in seconds)
% 5.14/1.99  ----------------------
% 5.14/1.99  Preprocessing        : 0.35
% 5.14/1.99  Parsing              : 0.19
% 5.14/1.99  CNF conversion       : 0.02
% 5.14/1.99  Main loop            : 0.87
% 5.14/1.99  Inferencing          : 0.31
% 5.14/1.99  Reduction            : 0.28
% 5.14/1.99  Demodulation         : 0.20
% 5.14/1.99  BG Simplification    : 0.03
% 5.14/1.99  Subsumption          : 0.17
% 5.14/1.99  Abstraction          : 0.04
% 5.14/1.99  MUC search           : 0.00
% 5.14/1.99  Cooper               : 0.00
% 5.14/1.99  Total                : 1.27
% 5.14/1.99  Index Insertion      : 0.00
% 5.14/1.99  Index Deletion       : 0.00
% 5.14/1.99  Index Matching       : 0.00
% 5.14/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
