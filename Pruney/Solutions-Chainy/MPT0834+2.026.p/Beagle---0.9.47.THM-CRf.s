%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:53 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 294 expanded)
%              Number of leaves         :   46 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  214 ( 535 expanded)
%              Number of equality atoms :   67 ( 145 expanded)
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

tff(f_135,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_100,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2794,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k8_relset_1(A_293,B_294,C_295,D_296) = k10_relat_1(C_295,D_296)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2797,plain,(
    ! [D_296] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_296) = k10_relat_1('#skF_3',D_296) ),
    inference(resolution,[status(thm)],[c_60,c_2794])).

tff(c_1871,plain,(
    ! [A_225,B_226,C_227] :
      ( k1_relset_1(A_225,B_226,C_227) = k1_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1875,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1871])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_139,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_139])).

tff(c_145,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_142])).

tff(c_179,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_183,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_179])).

tff(c_184,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,A_83) = B_82
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_187,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_184])).

tff(c_193,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_187])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_200,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_18])).

tff(c_204,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_200])).

tff(c_1578,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k7_relset_1(A_181,B_182,C_183,D_184) = k9_relat_1(C_183,D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1581,plain,(
    ! [D_184] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_184) = k9_relat_1('#skF_3',D_184) ),
    inference(resolution,[status(thm)],[c_60,c_1578])).

tff(c_782,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_786,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_782])).

tff(c_58,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_118,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_787,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_118])).

tff(c_1582,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_787])).

tff(c_1585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_1582])).

tff(c_1586,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1876,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1875,c_1586])).

tff(c_2798,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2797,c_1876])).

tff(c_1748,plain,(
    ! [C_213,B_214,A_215] :
      ( v5_relat_1(C_213,B_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1752,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1748])).

tff(c_1612,plain,(
    ! [B_191,A_192] :
      ( v1_relat_1(B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(A_192))
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1615,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_1612])).

tff(c_1618,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1615])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3083,plain,(
    ! [D_305,B_306,C_307,A_308] :
      ( m1_subset_1(D_305,k1_zfmisc_1(k2_zfmisc_1(B_306,C_307)))
      | ~ r1_tarski(k1_relat_1(D_305),B_306)
      | ~ m1_subset_1(D_305,k1_zfmisc_1(k2_zfmisc_1(A_308,C_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3087,plain,(
    ! [B_309] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_309,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_309) ) ),
    inference(resolution,[status(thm)],[c_60,c_3083])).

tff(c_46,plain,(
    ! [C_35,A_33,B_34] :
      ( v4_relat_1(C_35,A_33)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3120,plain,(
    ! [B_310] :
      ( v4_relat_1('#skF_3',B_310)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_310) ) ),
    inference(resolution,[status(thm)],[c_3087,c_46])).

tff(c_3135,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_3120])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3140,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3135,c_26])).

tff(c_3146,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_3140])).

tff(c_3166,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3146,c_18])).

tff(c_3170,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_3166])).

tff(c_40,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,k10_relat_1(B_30,k9_relat_1(B_30,A_29)))
      | ~ r1_tarski(A_29,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3175,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3170,c_40])).

tff(c_3179,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_8,c_3175])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k10_relat_1(B_18,A_17),k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1599,plain,(
    ! [B_189,A_190] :
      ( B_189 = A_190
      | ~ r1_tarski(B_189,A_190)
      | ~ r1_tarski(A_190,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3356,plain,(
    ! [B_318,A_319] :
      ( k10_relat_1(B_318,A_319) = k1_relat_1(B_318)
      | ~ r1_tarski(k1_relat_1(B_318),k10_relat_1(B_318,A_319))
      | ~ v1_relat_1(B_318) ) ),
    inference(resolution,[status(thm)],[c_22,c_1599])).

tff(c_3359,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3179,c_3356])).

tff(c_3388,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_3359])).

tff(c_1619,plain,(
    ! [C_193,A_194,B_195] :
      ( v4_relat_1(C_193,A_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1623,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1619])).

tff(c_1660,plain,(
    ! [B_204,A_205] :
      ( k7_relat_1(B_204,A_205) = B_204
      | ~ v4_relat_1(B_204,A_205)
      | ~ v1_relat_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1663,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1623,c_1660])).

tff(c_1669,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1663])).

tff(c_1676,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_18])).

tff(c_1680,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1676])).

tff(c_1642,plain,(
    ! [B_200,A_201] :
      ( r1_tarski(k2_relat_1(B_200),A_201)
      | ~ v5_relat_1(B_200,A_201)
      | ~ v1_relat_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3972,plain,(
    ! [B_345,A_346,A_347] :
      ( r1_tarski(k9_relat_1(B_345,A_346),A_347)
      | ~ v5_relat_1(k7_relat_1(B_345,A_346),A_347)
      | ~ v1_relat_1(k7_relat_1(B_345,A_346))
      | ~ v1_relat_1(B_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1642])).

tff(c_3997,plain,(
    ! [A_347] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_347)
      | ~ v5_relat_1('#skF_3',A_347)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_3972])).

tff(c_4012,plain,(
    ! [A_348] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_348)
      | ~ v5_relat_1('#skF_3',A_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1618,c_1669,c_1680,c_3997])).

tff(c_34,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [B_32,A_31] : k5_relat_1(k6_relat_1(B_32),k6_relat_1(A_31)) = k6_relat_1(k3_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1987,plain,(
    ! [B_240,A_241] :
      ( k9_relat_1(B_240,k2_relat_1(A_241)) = k2_relat_1(k5_relat_1(A_241,B_240))
      | ~ v1_relat_1(B_240)
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2015,plain,(
    ! [A_27,B_240] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_27),B_240)) = k9_relat_1(B_240,A_27)
      | ~ v1_relat_1(B_240)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1987])).

tff(c_2028,plain,(
    ! [A_242,B_243] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_242),B_243)) = k9_relat_1(B_243,A_242)
      | ~ v1_relat_1(B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2015])).

tff(c_2052,plain,(
    ! [A_31,B_32] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_31,B_32))) = k9_relat_1(k6_relat_1(A_31),B_32)
      | ~ v1_relat_1(k6_relat_1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2028])).

tff(c_2056,plain,(
    ! [A_31,B_32] : k9_relat_1(k6_relat_1(A_31),B_32) = k3_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2052])).

tff(c_36,plain,(
    ! [A_28] : v4_relat_1(k6_relat_1(A_28),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1860,plain,(
    ! [C_222,B_223,A_224] :
      ( v4_relat_1(C_222,B_223)
      | ~ v4_relat_1(C_222,A_224)
      | ~ v1_relat_1(C_222)
      | ~ r1_tarski(A_224,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1864,plain,(
    ! [A_28,B_223] :
      ( v4_relat_1(k6_relat_1(A_28),B_223)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ r1_tarski(A_28,B_223) ) ),
    inference(resolution,[status(thm)],[c_36,c_1860])).

tff(c_1893,plain,(
    ! [A_229,B_230] :
      ( v4_relat_1(k6_relat_1(A_229),B_230)
      | ~ r1_tarski(A_229,B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1864])).

tff(c_1898,plain,(
    ! [A_229,B_230] :
      ( k7_relat_1(k6_relat_1(A_229),B_230) = k6_relat_1(A_229)
      | ~ v1_relat_1(k6_relat_1(A_229))
      | ~ r1_tarski(A_229,B_230) ) ),
    inference(resolution,[status(thm)],[c_1893,c_26])).

tff(c_1912,plain,(
    ! [A_232,B_233] :
      ( k7_relat_1(k6_relat_1(A_232),B_233) = k6_relat_1(A_232)
      | ~ r1_tarski(A_232,B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1898])).

tff(c_1922,plain,(
    ! [A_232,B_233] :
      ( k9_relat_1(k6_relat_1(A_232),B_233) = k2_relat_1(k6_relat_1(A_232))
      | ~ v1_relat_1(k6_relat_1(A_232))
      | ~ r1_tarski(A_232,B_233) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1912,c_18])).

tff(c_1934,plain,(
    ! [A_232,B_233] :
      ( k9_relat_1(k6_relat_1(A_232),B_233) = A_232
      | ~ r1_tarski(A_232,B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1922])).

tff(c_2057,plain,(
    ! [A_232,B_233] :
      ( k3_xboole_0(A_232,B_233) = A_232
      | ~ r1_tarski(A_232,B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1934])).

tff(c_4055,plain,(
    ! [A_349] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_349) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_349) ) ),
    inference(resolution,[status(thm)],[c_4012,c_2057])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(B_20,k3_xboole_0(k2_relat_1(B_20),A_19)) = k10_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4090,plain,(
    ! [A_349] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_349)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4055,c_24])).

tff(c_4164,plain,(
    ! [A_351] :
      ( k10_relat_1('#skF_3',A_351) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_3388,c_4090])).

tff(c_4173,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1752,c_4164])).

tff(c_4184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2798,c_4173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.91  
% 4.74/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.91  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.74/1.91  
% 4.74/1.91  %Foreground sorts:
% 4.74/1.91  
% 4.74/1.91  
% 4.74/1.91  %Background operators:
% 4.74/1.91  
% 4.74/1.91  
% 4.74/1.91  %Foreground operators:
% 4.74/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.74/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.91  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.74/1.91  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.74/1.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.74/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.74/1.91  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.74/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.91  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.74/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.74/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.74/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.91  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.74/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.74/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.74/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.74/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.91  
% 5.07/1.93  tff(f_135, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 5.07/1.93  tff(f_122, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.07/1.93  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.07/1.93  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.07/1.93  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.07/1.93  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.07/1.93  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.07/1.93  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.07/1.93  tff(f_118, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.07/1.93  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.07/1.93  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.07/1.93  tff(f_128, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 5.07/1.93  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 5.07/1.93  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 5.07/1.93  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.07/1.93  tff(f_92, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 5.07/1.93  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.07/1.93  tff(f_100, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 5.07/1.93  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 5.07/1.93  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 5.07/1.93  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 5.07/1.93  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.07/1.93  tff(c_2794, plain, (![A_293, B_294, C_295, D_296]: (k8_relset_1(A_293, B_294, C_295, D_296)=k10_relat_1(C_295, D_296) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.07/1.93  tff(c_2797, plain, (![D_296]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_296)=k10_relat_1('#skF_3', D_296))), inference(resolution, [status(thm)], [c_60, c_2794])).
% 5.07/1.93  tff(c_1871, plain, (![A_225, B_226, C_227]: (k1_relset_1(A_225, B_226, C_227)=k1_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.07/1.93  tff(c_1875, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1871])).
% 5.07/1.93  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.07/1.93  tff(c_139, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.07/1.93  tff(c_142, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_139])).
% 5.07/1.93  tff(c_145, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_142])).
% 5.07/1.93  tff(c_179, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.07/1.93  tff(c_183, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_179])).
% 5.07/1.93  tff(c_184, plain, (![B_82, A_83]: (k7_relat_1(B_82, A_83)=B_82 | ~v4_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.07/1.93  tff(c_187, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_183, c_184])).
% 5.07/1.93  tff(c_193, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_187])).
% 5.07/1.93  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.07/1.93  tff(c_200, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193, c_18])).
% 5.07/1.93  tff(c_204, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_200])).
% 5.07/1.93  tff(c_1578, plain, (![A_181, B_182, C_183, D_184]: (k7_relset_1(A_181, B_182, C_183, D_184)=k9_relat_1(C_183, D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.07/1.93  tff(c_1581, plain, (![D_184]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_184)=k9_relat_1('#skF_3', D_184))), inference(resolution, [status(thm)], [c_60, c_1578])).
% 5.07/1.93  tff(c_782, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.07/1.94  tff(c_786, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_782])).
% 5.07/1.94  tff(c_58, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.07/1.94  tff(c_118, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 5.07/1.94  tff(c_787, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_118])).
% 5.07/1.94  tff(c_1582, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_787])).
% 5.07/1.94  tff(c_1585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_1582])).
% 5.07/1.94  tff(c_1586, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 5.07/1.94  tff(c_1876, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1875, c_1586])).
% 5.07/1.94  tff(c_2798, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2797, c_1876])).
% 5.07/1.94  tff(c_1748, plain, (![C_213, B_214, A_215]: (v5_relat_1(C_213, B_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.07/1.94  tff(c_1752, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1748])).
% 5.07/1.94  tff(c_1612, plain, (![B_191, A_192]: (v1_relat_1(B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(A_192)) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.07/1.94  tff(c_1615, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_1612])).
% 5.07/1.94  tff(c_1618, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1615])).
% 5.07/1.94  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.07/1.94  tff(c_3083, plain, (![D_305, B_306, C_307, A_308]: (m1_subset_1(D_305, k1_zfmisc_1(k2_zfmisc_1(B_306, C_307))) | ~r1_tarski(k1_relat_1(D_305), B_306) | ~m1_subset_1(D_305, k1_zfmisc_1(k2_zfmisc_1(A_308, C_307))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.07/1.94  tff(c_3087, plain, (![B_309]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_309, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_309))), inference(resolution, [status(thm)], [c_60, c_3083])).
% 5.07/1.94  tff(c_46, plain, (![C_35, A_33, B_34]: (v4_relat_1(C_35, A_33) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.07/1.94  tff(c_3120, plain, (![B_310]: (v4_relat_1('#skF_3', B_310) | ~r1_tarski(k1_relat_1('#skF_3'), B_310))), inference(resolution, [status(thm)], [c_3087, c_46])).
% 5.07/1.94  tff(c_3135, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_3120])).
% 5.07/1.94  tff(c_26, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.07/1.94  tff(c_3140, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3135, c_26])).
% 5.07/1.94  tff(c_3146, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_3140])).
% 5.07/1.94  tff(c_3166, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3146, c_18])).
% 5.07/1.94  tff(c_3170, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_3166])).
% 5.07/1.94  tff(c_40, plain, (![A_29, B_30]: (r1_tarski(A_29, k10_relat_1(B_30, k9_relat_1(B_30, A_29))) | ~r1_tarski(A_29, k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.07/1.94  tff(c_3175, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3170, c_40])).
% 5.07/1.94  tff(c_3179, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_8, c_3175])).
% 5.07/1.94  tff(c_22, plain, (![B_18, A_17]: (r1_tarski(k10_relat_1(B_18, A_17), k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.07/1.94  tff(c_1599, plain, (![B_189, A_190]: (B_189=A_190 | ~r1_tarski(B_189, A_190) | ~r1_tarski(A_190, B_189))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.07/1.94  tff(c_3356, plain, (![B_318, A_319]: (k10_relat_1(B_318, A_319)=k1_relat_1(B_318) | ~r1_tarski(k1_relat_1(B_318), k10_relat_1(B_318, A_319)) | ~v1_relat_1(B_318))), inference(resolution, [status(thm)], [c_22, c_1599])).
% 5.07/1.94  tff(c_3359, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3179, c_3356])).
% 5.07/1.94  tff(c_3388, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_3359])).
% 5.07/1.94  tff(c_1619, plain, (![C_193, A_194, B_195]: (v4_relat_1(C_193, A_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.07/1.94  tff(c_1623, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1619])).
% 5.07/1.94  tff(c_1660, plain, (![B_204, A_205]: (k7_relat_1(B_204, A_205)=B_204 | ~v4_relat_1(B_204, A_205) | ~v1_relat_1(B_204))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.07/1.94  tff(c_1663, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1623, c_1660])).
% 5.07/1.94  tff(c_1669, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1663])).
% 5.07/1.94  tff(c_1676, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1669, c_18])).
% 5.07/1.94  tff(c_1680, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1676])).
% 5.07/1.94  tff(c_1642, plain, (![B_200, A_201]: (r1_tarski(k2_relat_1(B_200), A_201) | ~v5_relat_1(B_200, A_201) | ~v1_relat_1(B_200))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.07/1.94  tff(c_3972, plain, (![B_345, A_346, A_347]: (r1_tarski(k9_relat_1(B_345, A_346), A_347) | ~v5_relat_1(k7_relat_1(B_345, A_346), A_347) | ~v1_relat_1(k7_relat_1(B_345, A_346)) | ~v1_relat_1(B_345))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1642])).
% 5.07/1.94  tff(c_3997, plain, (![A_347]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_347) | ~v5_relat_1('#skF_3', A_347) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1669, c_3972])).
% 5.07/1.94  tff(c_4012, plain, (![A_348]: (r1_tarski(k2_relat_1('#skF_3'), A_348) | ~v5_relat_1('#skF_3', A_348))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1618, c_1669, c_1680, c_3997])).
% 5.07/1.94  tff(c_34, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.07/1.94  tff(c_32, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.07/1.94  tff(c_42, plain, (![B_32, A_31]: (k5_relat_1(k6_relat_1(B_32), k6_relat_1(A_31))=k6_relat_1(k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.07/1.94  tff(c_1987, plain, (![B_240, A_241]: (k9_relat_1(B_240, k2_relat_1(A_241))=k2_relat_1(k5_relat_1(A_241, B_240)) | ~v1_relat_1(B_240) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.07/1.94  tff(c_2015, plain, (![A_27, B_240]: (k2_relat_1(k5_relat_1(k6_relat_1(A_27), B_240))=k9_relat_1(B_240, A_27) | ~v1_relat_1(B_240) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1987])).
% 5.07/1.94  tff(c_2028, plain, (![A_242, B_243]: (k2_relat_1(k5_relat_1(k6_relat_1(A_242), B_243))=k9_relat_1(B_243, A_242) | ~v1_relat_1(B_243))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2015])).
% 5.07/1.94  tff(c_2052, plain, (![A_31, B_32]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_31, B_32)))=k9_relat_1(k6_relat_1(A_31), B_32) | ~v1_relat_1(k6_relat_1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2028])).
% 5.07/1.94  tff(c_2056, plain, (![A_31, B_32]: (k9_relat_1(k6_relat_1(A_31), B_32)=k3_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2052])).
% 5.07/1.94  tff(c_36, plain, (![A_28]: (v4_relat_1(k6_relat_1(A_28), A_28))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.07/1.94  tff(c_1860, plain, (![C_222, B_223, A_224]: (v4_relat_1(C_222, B_223) | ~v4_relat_1(C_222, A_224) | ~v1_relat_1(C_222) | ~r1_tarski(A_224, B_223))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.07/1.94  tff(c_1864, plain, (![A_28, B_223]: (v4_relat_1(k6_relat_1(A_28), B_223) | ~v1_relat_1(k6_relat_1(A_28)) | ~r1_tarski(A_28, B_223))), inference(resolution, [status(thm)], [c_36, c_1860])).
% 5.07/1.94  tff(c_1893, plain, (![A_229, B_230]: (v4_relat_1(k6_relat_1(A_229), B_230) | ~r1_tarski(A_229, B_230))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1864])).
% 5.07/1.94  tff(c_1898, plain, (![A_229, B_230]: (k7_relat_1(k6_relat_1(A_229), B_230)=k6_relat_1(A_229) | ~v1_relat_1(k6_relat_1(A_229)) | ~r1_tarski(A_229, B_230))), inference(resolution, [status(thm)], [c_1893, c_26])).
% 5.07/1.94  tff(c_1912, plain, (![A_232, B_233]: (k7_relat_1(k6_relat_1(A_232), B_233)=k6_relat_1(A_232) | ~r1_tarski(A_232, B_233))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1898])).
% 5.07/1.94  tff(c_1922, plain, (![A_232, B_233]: (k9_relat_1(k6_relat_1(A_232), B_233)=k2_relat_1(k6_relat_1(A_232)) | ~v1_relat_1(k6_relat_1(A_232)) | ~r1_tarski(A_232, B_233))), inference(superposition, [status(thm), theory('equality')], [c_1912, c_18])).
% 5.07/1.94  tff(c_1934, plain, (![A_232, B_233]: (k9_relat_1(k6_relat_1(A_232), B_233)=A_232 | ~r1_tarski(A_232, B_233))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1922])).
% 5.07/1.94  tff(c_2057, plain, (![A_232, B_233]: (k3_xboole_0(A_232, B_233)=A_232 | ~r1_tarski(A_232, B_233))), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1934])).
% 5.07/1.94  tff(c_4055, plain, (![A_349]: (k3_xboole_0(k2_relat_1('#skF_3'), A_349)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_349))), inference(resolution, [status(thm)], [c_4012, c_2057])).
% 5.07/1.94  tff(c_24, plain, (![B_20, A_19]: (k10_relat_1(B_20, k3_xboole_0(k2_relat_1(B_20), A_19))=k10_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.07/1.94  tff(c_4090, plain, (![A_349]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_349) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_349))), inference(superposition, [status(thm), theory('equality')], [c_4055, c_24])).
% 5.07/1.94  tff(c_4164, plain, (![A_351]: (k10_relat_1('#skF_3', A_351)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_351))), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_3388, c_4090])).
% 5.07/1.94  tff(c_4173, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1752, c_4164])).
% 5.07/1.94  tff(c_4184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2798, c_4173])).
% 5.07/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/1.94  
% 5.07/1.94  Inference rules
% 5.07/1.94  ----------------------
% 5.07/1.94  #Ref     : 0
% 5.07/1.94  #Sup     : 902
% 5.07/1.94  #Fact    : 0
% 5.07/1.94  #Define  : 0
% 5.07/1.94  #Split   : 4
% 5.07/1.94  #Chain   : 0
% 5.07/1.94  #Close   : 0
% 5.07/1.94  
% 5.07/1.94  Ordering : KBO
% 5.07/1.94  
% 5.07/1.94  Simplification rules
% 5.07/1.94  ----------------------
% 5.07/1.94  #Subsume      : 123
% 5.07/1.94  #Demod        : 808
% 5.07/1.94  #Tautology    : 425
% 5.07/1.94  #SimpNegUnit  : 1
% 5.07/1.94  #BackRed      : 17
% 5.07/1.94  
% 5.07/1.94  #Partial instantiations: 0
% 5.07/1.94  #Strategies tried      : 1
% 5.07/1.94  
% 5.07/1.94  Timing (in seconds)
% 5.07/1.94  ----------------------
% 5.07/1.94  Preprocessing        : 0.35
% 5.07/1.94  Parsing              : 0.18
% 5.07/1.94  CNF conversion       : 0.02
% 5.07/1.94  Main loop            : 0.81
% 5.07/1.94  Inferencing          : 0.30
% 5.07/1.94  Reduction            : 0.29
% 5.07/1.94  Demodulation         : 0.22
% 5.07/1.94  BG Simplification    : 0.03
% 5.07/1.94  Subsumption          : 0.13
% 5.07/1.94  Abstraction          : 0.04
% 5.07/1.94  MUC search           : 0.00
% 5.07/1.94  Cooper               : 0.00
% 5.07/1.94  Total                : 1.20
% 5.07/1.94  Index Insertion      : 0.00
% 5.07/1.94  Index Deletion       : 0.00
% 5.07/1.94  Index Matching       : 0.00
% 5.07/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
