%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:54 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 128 expanded)
%              Number of leaves         :   40 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 200 expanded)
%              Number of equality atoms :   48 (  75 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_44,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1119,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k8_relset_1(A_208,B_209,C_210,D_211) = k10_relat_1(C_210,D_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1130,plain,(
    ! [D_211] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_211) = k10_relat_1('#skF_3',D_211) ),
    inference(resolution,[status(thm)],[c_44,c_1119])).

tff(c_803,plain,(
    ! [A_173,B_174,C_175] :
      ( k1_relset_1(A_173,B_174,C_175) = k1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_812,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_803])).

tff(c_14,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_75])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_269,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_278,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_269])).

tff(c_511,plain,(
    ! [A_124,B_125,C_126] :
      ( m1_subset_1(k1_relset_1(A_124,B_125,C_126),k1_zfmisc_1(A_124))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_536,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_511])).

tff(c_544,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_536])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_552,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_544,c_2])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_559,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_552,c_24])).

tff(c_567,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_559])).

tff(c_12,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_405,plain,(
    ! [B_114,A_115] :
      ( k9_relat_1(B_114,k2_relat_1(A_115)) = k2_relat_1(k5_relat_1(A_115,B_114))
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_414,plain,(
    ! [A_17,B_114] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_17),B_114)) = k9_relat_1(B_114,A_17)
      | ~ v1_relat_1(B_114)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_405])).

tff(c_418,plain,(
    ! [A_17,B_114] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_17),B_114)) = k9_relat_1(B_114,A_17)
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_414])).

tff(c_573,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_418])).

tff(c_577,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_573])).

tff(c_584,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k7_relset_1(A_127,B_128,C_129,D_130) = k9_relat_1(C_129,D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_595,plain,(
    ! [D_130] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_130) = k9_relat_1('#skF_3',D_130) ),
    inference(resolution,[status(thm)],[c_44,c_584])).

tff(c_300,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_309,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_300])).

tff(c_42,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_86,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_310,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_86])).

tff(c_596,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_310])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_596])).

tff(c_600,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_813,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_600])).

tff(c_1131,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_813])).

tff(c_609,plain,(
    ! [C_133,B_134,A_135] :
      ( v5_relat_1(C_133,B_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_618,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_609])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_699,plain,(
    ! [B_157,A_158] :
      ( k5_relat_1(B_157,k6_relat_1(A_158)) = B_157
      | ~ r1_tarski(k2_relat_1(B_157),A_158)
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_706,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_699])).

tff(c_20,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_850,plain,(
    ! [A_187,B_188] :
      ( k10_relat_1(A_187,k1_relat_1(B_188)) = k1_relat_1(k5_relat_1(A_187,B_188))
      | ~ v1_relat_1(B_188)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_859,plain,(
    ! [A_187,A_17] :
      ( k1_relat_1(k5_relat_1(A_187,k6_relat_1(A_17))) = k10_relat_1(A_187,A_17)
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(A_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_850])).

tff(c_864,plain,(
    ! [A_189,A_190] :
      ( k1_relat_1(k5_relat_1(A_189,k6_relat_1(A_190))) = k10_relat_1(A_189,A_190)
      | ~ v1_relat_1(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_859])).

tff(c_1195,plain,(
    ! [B_221,A_222] :
      ( k10_relat_1(B_221,A_222) = k1_relat_1(B_221)
      | ~ v1_relat_1(B_221)
      | ~ v5_relat_1(B_221,A_222)
      | ~ v1_relat_1(B_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_864])).

tff(c_1201,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_618,c_1195])).

tff(c_1207,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1201])).

tff(c_1209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1131,c_1207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.51  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.51  
% 3.15/1.51  %Foreground sorts:
% 3.15/1.51  
% 3.15/1.51  
% 3.15/1.51  %Background operators:
% 3.15/1.51  
% 3.15/1.51  
% 3.15/1.51  %Foreground operators:
% 3.15/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.15/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.15/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.15/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.15/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.15/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.15/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.15/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.51  
% 3.15/1.53  tff(f_109, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.15/1.53  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.15/1.53  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.53  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.15/1.53  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.15/1.53  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.15/1.53  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.15/1.53  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.15/1.53  tff(f_44, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.15/1.53  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.15/1.53  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.15/1.53  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.15/1.53  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.15/1.53  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.15/1.53  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.15/1.53  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.15/1.53  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.15/1.53  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.15/1.53  tff(c_1119, plain, (![A_208, B_209, C_210, D_211]: (k8_relset_1(A_208, B_209, C_210, D_211)=k10_relat_1(C_210, D_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.53  tff(c_1130, plain, (![D_211]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_211)=k10_relat_1('#skF_3', D_211))), inference(resolution, [status(thm)], [c_44, c_1119])).
% 3.15/1.53  tff(c_803, plain, (![A_173, B_174, C_175]: (k1_relset_1(A_173, B_174, C_175)=k1_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.53  tff(c_812, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_803])).
% 3.15/1.53  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.53  tff(c_75, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.15/1.53  tff(c_81, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_75])).
% 3.15/1.53  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_81])).
% 3.15/1.53  tff(c_269, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.15/1.53  tff(c_278, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_269])).
% 3.15/1.53  tff(c_511, plain, (![A_124, B_125, C_126]: (m1_subset_1(k1_relset_1(A_124, B_125, C_126), k1_zfmisc_1(A_124)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.53  tff(c_536, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_278, c_511])).
% 3.15/1.53  tff(c_544, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_536])).
% 3.15/1.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.53  tff(c_552, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_544, c_2])).
% 3.15/1.53  tff(c_24, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.53  tff(c_559, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_552, c_24])).
% 3.15/1.53  tff(c_567, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_559])).
% 3.15/1.53  tff(c_12, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.53  tff(c_22, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.53  tff(c_405, plain, (![B_114, A_115]: (k9_relat_1(B_114, k2_relat_1(A_115))=k2_relat_1(k5_relat_1(A_115, B_114)) | ~v1_relat_1(B_114) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.15/1.53  tff(c_414, plain, (![A_17, B_114]: (k2_relat_1(k5_relat_1(k6_relat_1(A_17), B_114))=k9_relat_1(B_114, A_17) | ~v1_relat_1(B_114) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_405])).
% 3.15/1.53  tff(c_418, plain, (![A_17, B_114]: (k2_relat_1(k5_relat_1(k6_relat_1(A_17), B_114))=k9_relat_1(B_114, A_17) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_414])).
% 3.15/1.53  tff(c_573, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_567, c_418])).
% 3.15/1.53  tff(c_577, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_573])).
% 3.15/1.53  tff(c_584, plain, (![A_127, B_128, C_129, D_130]: (k7_relset_1(A_127, B_128, C_129, D_130)=k9_relat_1(C_129, D_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.15/1.53  tff(c_595, plain, (![D_130]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_130)=k9_relat_1('#skF_3', D_130))), inference(resolution, [status(thm)], [c_44, c_584])).
% 3.15/1.53  tff(c_300, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.15/1.53  tff(c_309, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_300])).
% 3.15/1.53  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.15/1.53  tff(c_86, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.15/1.53  tff(c_310, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_86])).
% 3.15/1.53  tff(c_596, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_595, c_310])).
% 3.15/1.53  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_596])).
% 3.15/1.53  tff(c_600, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.15/1.53  tff(c_813, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_812, c_600])).
% 3.15/1.53  tff(c_1131, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_813])).
% 3.15/1.53  tff(c_609, plain, (![C_133, B_134, A_135]: (v5_relat_1(C_133, B_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.53  tff(c_618, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_609])).
% 3.15/1.53  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.53  tff(c_699, plain, (![B_157, A_158]: (k5_relat_1(B_157, k6_relat_1(A_158))=B_157 | ~r1_tarski(k2_relat_1(B_157), A_158) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.53  tff(c_706, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_10, c_699])).
% 3.15/1.53  tff(c_20, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.53  tff(c_850, plain, (![A_187, B_188]: (k10_relat_1(A_187, k1_relat_1(B_188))=k1_relat_1(k5_relat_1(A_187, B_188)) | ~v1_relat_1(B_188) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.53  tff(c_859, plain, (![A_187, A_17]: (k1_relat_1(k5_relat_1(A_187, k6_relat_1(A_17)))=k10_relat_1(A_187, A_17) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(A_187))), inference(superposition, [status(thm), theory('equality')], [c_20, c_850])).
% 3.15/1.53  tff(c_864, plain, (![A_189, A_190]: (k1_relat_1(k5_relat_1(A_189, k6_relat_1(A_190)))=k10_relat_1(A_189, A_190) | ~v1_relat_1(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_859])).
% 3.15/1.53  tff(c_1195, plain, (![B_221, A_222]: (k10_relat_1(B_221, A_222)=k1_relat_1(B_221) | ~v1_relat_1(B_221) | ~v5_relat_1(B_221, A_222) | ~v1_relat_1(B_221))), inference(superposition, [status(thm), theory('equality')], [c_706, c_864])).
% 3.15/1.53  tff(c_1201, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_618, c_1195])).
% 3.15/1.53  tff(c_1207, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1201])).
% 3.15/1.53  tff(c_1209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1131, c_1207])).
% 3.15/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.53  
% 3.15/1.53  Inference rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Ref     : 0
% 3.15/1.53  #Sup     : 252
% 3.15/1.53  #Fact    : 0
% 3.15/1.53  #Define  : 0
% 3.15/1.53  #Split   : 9
% 3.15/1.53  #Chain   : 0
% 3.15/1.53  #Close   : 0
% 3.15/1.53  
% 3.15/1.53  Ordering : KBO
% 3.15/1.53  
% 3.15/1.53  Simplification rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Subsume      : 25
% 3.15/1.53  #Demod        : 103
% 3.15/1.53  #Tautology    : 90
% 3.15/1.53  #SimpNegUnit  : 1
% 3.15/1.53  #BackRed      : 5
% 3.15/1.53  
% 3.15/1.53  #Partial instantiations: 0
% 3.15/1.53  #Strategies tried      : 1
% 3.15/1.53  
% 3.15/1.53  Timing (in seconds)
% 3.15/1.53  ----------------------
% 3.15/1.53  Preprocessing        : 0.33
% 3.15/1.53  Parsing              : 0.18
% 3.15/1.53  CNF conversion       : 0.02
% 3.15/1.53  Main loop            : 0.41
% 3.15/1.53  Inferencing          : 0.16
% 3.15/1.53  Reduction            : 0.12
% 3.15/1.53  Demodulation         : 0.08
% 3.15/1.53  BG Simplification    : 0.02
% 3.15/1.53  Subsumption          : 0.06
% 3.15/1.53  Abstraction          : 0.02
% 3.15/1.53  MUC search           : 0.00
% 3.15/1.53  Cooper               : 0.00
% 3.15/1.53  Total                : 0.77
% 3.15/1.53  Index Insertion      : 0.00
% 3.15/1.53  Index Deletion       : 0.00
% 3.15/1.53  Index Matching       : 0.00
% 3.15/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
