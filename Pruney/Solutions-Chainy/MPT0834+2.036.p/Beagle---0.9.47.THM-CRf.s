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
% DateTime   : Thu Dec  3 10:07:54 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 231 expanded)
%              Number of leaves         :   43 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  155 ( 402 expanded)
%              Number of equality atoms :   58 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_83,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1485,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k8_relset_1(A_203,B_204,C_205,D_206) = k10_relat_1(C_205,D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1488,plain,(
    ! [D_206] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_206) = k10_relat_1('#skF_3',D_206) ),
    inference(resolution,[status(thm)],[c_48,c_1485])).

tff(c_1414,plain,(
    ! [A_195,B_196,C_197] :
      ( k1_relset_1(A_195,B_196,C_197) = k1_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1418,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1414])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_205,plain,(
    ! [C_63,A_64,B_65] :
      ( v4_relat_1(C_63,A_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_209,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_205])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_212,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_209,c_16])).

tff(c_215,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_212])).

tff(c_270,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(k7_relat_1(B_79,A_80)) = k9_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_291,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_270])).

tff(c_298,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_291])).

tff(c_730,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k7_relset_1(A_123,B_124,C_125,D_126) = k9_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_733,plain,(
    ! [D_126] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_126) = k9_relat_1('#skF_3',D_126) ),
    inference(resolution,[status(thm)],[c_48,c_730])).

tff(c_611,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_615,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_611])).

tff(c_46,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_78,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_616,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_78])).

tff(c_734,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_616])).

tff(c_737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_734])).

tff(c_738,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1419,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_738])).

tff(c_1489,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1419])).

tff(c_994,plain,(
    ! [C_155,B_156,A_157] :
      ( v5_relat_1(C_155,B_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_998,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_994])).

tff(c_804,plain,(
    ! [C_139,A_140,B_141] :
      ( v4_relat_1(C_139,A_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_808,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_804])).

tff(c_811,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_808,c_16])).

tff(c_814,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_811])).

tff(c_888,plain,(
    ! [B_151,A_152] :
      ( k2_relat_1(k7_relat_1(B_151,A_152)) = k9_relat_1(B_151,A_152)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_912,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_888])).

tff(c_921,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_912])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2372,plain,(
    ! [B_240,A_241,A_242] :
      ( r1_tarski(k9_relat_1(B_240,A_241),A_242)
      | ~ v5_relat_1(k7_relat_1(B_240,A_241),A_242)
      | ~ v1_relat_1(k7_relat_1(B_240,A_241))
      | ~ v1_relat_1(B_240) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_6])).

tff(c_2388,plain,(
    ! [A_242] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_242)
      | ~ v5_relat_1('#skF_3',A_242)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_814,c_2372])).

tff(c_2403,plain,(
    ! [A_243] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_243)
      | ~ v5_relat_1('#skF_3',A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_814,c_921,c_2388])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_852,plain,(
    ! [B_147,A_148] : k5_relat_1(k6_relat_1(B_147),k6_relat_1(A_148)) = k6_relat_1(k3_xboole_0(A_148,B_147)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_858,plain,(
    ! [A_148,B_147] :
      ( k7_relat_1(k6_relat_1(A_148),B_147) = k6_relat_1(k3_xboole_0(A_148,B_147))
      | ~ v1_relat_1(k6_relat_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_24])).

tff(c_868,plain,(
    ! [A_148,B_147] : k7_relat_1(k6_relat_1(A_148),B_147) = k6_relat_1(k3_xboole_0(A_148,B_147)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_858])).

tff(c_28,plain,(
    ! [A_22] : v4_relat_1(k6_relat_1(A_22),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1012,plain,(
    ! [C_159,B_160,A_161] :
      ( v4_relat_1(C_159,B_160)
      | ~ v4_relat_1(C_159,A_161)
      | ~ v1_relat_1(C_159)
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1016,plain,(
    ! [A_22,B_160] :
      ( v4_relat_1(k6_relat_1(A_22),B_160)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ r1_tarski(A_22,B_160) ) ),
    inference(resolution,[status(thm)],[c_28,c_1012])).

tff(c_1036,plain,(
    ! [A_163,B_164] :
      ( v4_relat_1(k6_relat_1(A_163),B_164)
      | ~ r1_tarski(A_163,B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1016])).

tff(c_1041,plain,(
    ! [A_163,B_164] :
      ( k7_relat_1(k6_relat_1(A_163),B_164) = k6_relat_1(A_163)
      | ~ v1_relat_1(k6_relat_1(A_163))
      | ~ r1_tarski(A_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_1036,c_16])).

tff(c_1075,plain,(
    ! [A_168,B_169] :
      ( k6_relat_1(k3_xboole_0(A_168,B_169)) = k6_relat_1(A_168)
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_868,c_1041])).

tff(c_1114,plain,(
    ! [A_168,B_169] :
      ( k3_xboole_0(A_168,B_169) = k1_relat_1(k6_relat_1(A_168))
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_20])).

tff(c_1139,plain,(
    ! [A_168,B_169] :
      ( k3_xboole_0(A_168,B_169) = A_168
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1114])).

tff(c_2425,plain,(
    ! [A_244] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_244) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_244) ) ),
    inference(resolution,[status(thm)],[c_2403,c_1139])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k10_relat_1(B_11,k3_xboole_0(k2_relat_1(B_11),A_10)) = k10_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2510,plain,(
    ! [A_244] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_244)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_244) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2425,c_12])).

tff(c_2596,plain,(
    ! [A_247] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_247)
      | ~ v5_relat_1('#skF_3',A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2510])).

tff(c_2602,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_998,c_2596])).

tff(c_14,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2611,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2602,c_14])).

tff(c_2618,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2611])).

tff(c_2620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_2618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.66  
% 3.89/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.66  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.89/1.66  
% 3.89/1.66  %Foreground sorts:
% 3.89/1.66  
% 3.89/1.66  
% 3.89/1.66  %Background operators:
% 3.89/1.66  
% 3.89/1.66  
% 3.89/1.66  %Foreground operators:
% 3.89/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.89/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.89/1.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.89/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.89/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.89/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.89/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.89/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.89/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.89/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.89/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.89/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.89/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.89/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.89/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.66  
% 4.01/1.68  tff(f_112, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.01/1.68  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.01/1.68  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.01/1.68  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.01/1.68  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.01/1.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.01/1.68  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.01/1.68  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.01/1.68  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.01/1.68  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.01/1.68  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.01/1.68  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.01/1.68  tff(f_81, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 4.01/1.68  tff(f_83, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 4.01/1.68  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 4.01/1.68  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 4.01/1.68  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 4.01/1.68  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.01/1.68  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.01/1.68  tff(c_1485, plain, (![A_203, B_204, C_205, D_206]: (k8_relset_1(A_203, B_204, C_205, D_206)=k10_relat_1(C_205, D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.68  tff(c_1488, plain, (![D_206]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_206)=k10_relat_1('#skF_3', D_206))), inference(resolution, [status(thm)], [c_48, c_1485])).
% 4.01/1.68  tff(c_1414, plain, (![A_195, B_196, C_197]: (k1_relset_1(A_195, B_196, C_197)=k1_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.68  tff(c_1418, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1414])).
% 4.01/1.68  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.01/1.68  tff(c_71, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.68  tff(c_74, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 4.01/1.68  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_74])).
% 4.01/1.68  tff(c_205, plain, (![C_63, A_64, B_65]: (v4_relat_1(C_63, A_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.01/1.68  tff(c_209, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_205])).
% 4.01/1.68  tff(c_16, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.01/1.68  tff(c_212, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_209, c_16])).
% 4.01/1.68  tff(c_215, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_212])).
% 4.01/1.68  tff(c_270, plain, (![B_79, A_80]: (k2_relat_1(k7_relat_1(B_79, A_80))=k9_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.01/1.68  tff(c_291, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_215, c_270])).
% 4.01/1.68  tff(c_298, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_291])).
% 4.01/1.68  tff(c_730, plain, (![A_123, B_124, C_125, D_126]: (k7_relset_1(A_123, B_124, C_125, D_126)=k9_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.68  tff(c_733, plain, (![D_126]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_126)=k9_relat_1('#skF_3', D_126))), inference(resolution, [status(thm)], [c_48, c_730])).
% 4.01/1.68  tff(c_611, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.01/1.68  tff(c_615, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_611])).
% 4.01/1.68  tff(c_46, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.01/1.68  tff(c_78, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 4.01/1.68  tff(c_616, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_615, c_78])).
% 4.01/1.68  tff(c_734, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_733, c_616])).
% 4.01/1.68  tff(c_737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_298, c_734])).
% 4.01/1.68  tff(c_738, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 4.01/1.68  tff(c_1419, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1418, c_738])).
% 4.01/1.68  tff(c_1489, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1419])).
% 4.01/1.68  tff(c_994, plain, (![C_155, B_156, A_157]: (v5_relat_1(C_155, B_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_156))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.01/1.68  tff(c_998, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_994])).
% 4.01/1.68  tff(c_804, plain, (![C_139, A_140, B_141]: (v4_relat_1(C_139, A_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.01/1.68  tff(c_808, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_804])).
% 4.01/1.68  tff(c_811, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_808, c_16])).
% 4.01/1.68  tff(c_814, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_811])).
% 4.01/1.68  tff(c_888, plain, (![B_151, A_152]: (k2_relat_1(k7_relat_1(B_151, A_152))=k9_relat_1(B_151, A_152) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.01/1.68  tff(c_912, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_814, c_888])).
% 4.01/1.68  tff(c_921, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_912])).
% 4.01/1.68  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.68  tff(c_2372, plain, (![B_240, A_241, A_242]: (r1_tarski(k9_relat_1(B_240, A_241), A_242) | ~v5_relat_1(k7_relat_1(B_240, A_241), A_242) | ~v1_relat_1(k7_relat_1(B_240, A_241)) | ~v1_relat_1(B_240))), inference(superposition, [status(thm), theory('equality')], [c_888, c_6])).
% 4.01/1.68  tff(c_2388, plain, (![A_242]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_242) | ~v5_relat_1('#skF_3', A_242) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_814, c_2372])).
% 4.01/1.68  tff(c_2403, plain, (![A_243]: (r1_tarski(k2_relat_1('#skF_3'), A_243) | ~v5_relat_1('#skF_3', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_814, c_921, c_2388])).
% 4.01/1.68  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.01/1.68  tff(c_26, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.01/1.68  tff(c_852, plain, (![B_147, A_148]: (k5_relat_1(k6_relat_1(B_147), k6_relat_1(A_148))=k6_relat_1(k3_xboole_0(A_148, B_147)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.68  tff(c_24, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.68  tff(c_858, plain, (![A_148, B_147]: (k7_relat_1(k6_relat_1(A_148), B_147)=k6_relat_1(k3_xboole_0(A_148, B_147)) | ~v1_relat_1(k6_relat_1(A_148)))), inference(superposition, [status(thm), theory('equality')], [c_852, c_24])).
% 4.01/1.68  tff(c_868, plain, (![A_148, B_147]: (k7_relat_1(k6_relat_1(A_148), B_147)=k6_relat_1(k3_xboole_0(A_148, B_147)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_858])).
% 4.01/1.68  tff(c_28, plain, (![A_22]: (v4_relat_1(k6_relat_1(A_22), A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.01/1.68  tff(c_1012, plain, (![C_159, B_160, A_161]: (v4_relat_1(C_159, B_160) | ~v4_relat_1(C_159, A_161) | ~v1_relat_1(C_159) | ~r1_tarski(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.01/1.68  tff(c_1016, plain, (![A_22, B_160]: (v4_relat_1(k6_relat_1(A_22), B_160) | ~v1_relat_1(k6_relat_1(A_22)) | ~r1_tarski(A_22, B_160))), inference(resolution, [status(thm)], [c_28, c_1012])).
% 4.01/1.68  tff(c_1036, plain, (![A_163, B_164]: (v4_relat_1(k6_relat_1(A_163), B_164) | ~r1_tarski(A_163, B_164))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1016])).
% 4.01/1.68  tff(c_1041, plain, (![A_163, B_164]: (k7_relat_1(k6_relat_1(A_163), B_164)=k6_relat_1(A_163) | ~v1_relat_1(k6_relat_1(A_163)) | ~r1_tarski(A_163, B_164))), inference(resolution, [status(thm)], [c_1036, c_16])).
% 4.01/1.68  tff(c_1075, plain, (![A_168, B_169]: (k6_relat_1(k3_xboole_0(A_168, B_169))=k6_relat_1(A_168) | ~r1_tarski(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_868, c_1041])).
% 4.01/1.68  tff(c_1114, plain, (![A_168, B_169]: (k3_xboole_0(A_168, B_169)=k1_relat_1(k6_relat_1(A_168)) | ~r1_tarski(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_20])).
% 4.01/1.68  tff(c_1139, plain, (![A_168, B_169]: (k3_xboole_0(A_168, B_169)=A_168 | ~r1_tarski(A_168, B_169))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1114])).
% 4.01/1.68  tff(c_2425, plain, (![A_244]: (k3_xboole_0(k2_relat_1('#skF_3'), A_244)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_244))), inference(resolution, [status(thm)], [c_2403, c_1139])).
% 4.01/1.68  tff(c_12, plain, (![B_11, A_10]: (k10_relat_1(B_11, k3_xboole_0(k2_relat_1(B_11), A_10))=k10_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.01/1.68  tff(c_2510, plain, (![A_244]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_244) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_244))), inference(superposition, [status(thm), theory('equality')], [c_2425, c_12])).
% 4.01/1.68  tff(c_2596, plain, (![A_247]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_247) | ~v5_relat_1('#skF_3', A_247))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2510])).
% 4.01/1.68  tff(c_2602, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_998, c_2596])).
% 4.01/1.68  tff(c_14, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.01/1.68  tff(c_2611, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2602, c_14])).
% 4.01/1.68  tff(c_2618, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2611])).
% 4.01/1.68  tff(c_2620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1489, c_2618])).
% 4.01/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.68  
% 4.01/1.68  Inference rules
% 4.01/1.68  ----------------------
% 4.01/1.68  #Ref     : 0
% 4.01/1.68  #Sup     : 600
% 4.01/1.68  #Fact    : 0
% 4.01/1.68  #Define  : 0
% 4.01/1.68  #Split   : 2
% 4.01/1.68  #Chain   : 0
% 4.01/1.68  #Close   : 0
% 4.01/1.68  
% 4.01/1.68  Ordering : KBO
% 4.01/1.68  
% 4.01/1.68  Simplification rules
% 4.01/1.68  ----------------------
% 4.01/1.68  #Subsume      : 72
% 4.01/1.68  #Demod        : 388
% 4.01/1.68  #Tautology    : 299
% 4.01/1.68  #SimpNegUnit  : 1
% 4.01/1.68  #BackRed      : 6
% 4.01/1.68  
% 4.01/1.68  #Partial instantiations: 0
% 4.01/1.68  #Strategies tried      : 1
% 4.01/1.68  
% 4.01/1.68  Timing (in seconds)
% 4.01/1.68  ----------------------
% 4.01/1.68  Preprocessing        : 0.32
% 4.01/1.68  Parsing              : 0.18
% 4.01/1.68  CNF conversion       : 0.02
% 4.01/1.68  Main loop            : 0.59
% 4.01/1.68  Inferencing          : 0.22
% 4.01/1.68  Reduction            : 0.20
% 4.01/1.68  Demodulation         : 0.14
% 4.01/1.68  BG Simplification    : 0.03
% 4.01/1.68  Subsumption          : 0.10
% 4.01/1.68  Abstraction          : 0.03
% 4.01/1.68  MUC search           : 0.00
% 4.01/1.68  Cooper               : 0.00
% 4.01/1.69  Total                : 0.96
% 4.01/1.69  Index Insertion      : 0.00
% 4.01/1.69  Index Deletion       : 0.00
% 4.01/1.69  Index Matching       : 0.00
% 4.01/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
