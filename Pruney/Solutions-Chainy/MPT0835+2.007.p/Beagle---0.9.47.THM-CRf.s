%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:56 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 206 expanded)
%              Number of leaves         :   40 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 356 expanded)
%              Number of equality atoms :   70 ( 136 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1569,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( k8_relset_1(A_255,B_256,C_257,D_258) = k10_relat_1(C_257,D_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1576,plain,(
    ! [D_258] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_258) = k10_relat_1('#skF_3',D_258) ),
    inference(resolution,[status(thm)],[c_50,c_1569])).

tff(c_1717,plain,(
    ! [A_287,B_288,C_289] :
      ( k8_relset_1(A_287,B_288,C_289,B_288) = k1_relset_1(A_287,B_288,C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1722,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1717])).

tff(c_1725,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_1722])).

tff(c_970,plain,(
    ! [C_177,A_178,B_179] :
      ( v1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_979,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_970])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1125,plain,(
    ! [B_210,A_211] :
      ( k5_relat_1(B_210,k6_relat_1(A_211)) = B_210
      | ~ r1_tarski(k2_relat_1(B_210),A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1142,plain,(
    ! [B_210] :
      ( k5_relat_1(B_210,k6_relat_1(k2_relat_1(B_210))) = B_210
      | ~ v1_relat_1(B_210) ) ),
    inference(resolution,[status(thm)],[c_6,c_1125])).

tff(c_16,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1252,plain,(
    ! [A_225,B_226] :
      ( k10_relat_1(A_225,k1_relat_1(B_226)) = k1_relat_1(k5_relat_1(A_225,B_226))
      | ~ v1_relat_1(B_226)
      | ~ v1_relat_1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1261,plain,(
    ! [A_225,A_15] :
      ( k1_relat_1(k5_relat_1(A_225,k6_relat_1(A_15))) = k10_relat_1(A_225,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1252])).

tff(c_1310,plain,(
    ! [A_229,A_230] :
      ( k1_relat_1(k5_relat_1(A_229,k6_relat_1(A_230))) = k10_relat_1(A_229,A_230)
      | ~ v1_relat_1(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1261])).

tff(c_1331,plain,(
    ! [B_210] :
      ( k10_relat_1(B_210,k2_relat_1(B_210)) = k1_relat_1(B_210)
      | ~ v1_relat_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_1310])).

tff(c_1096,plain,(
    ! [C_207,A_208,B_209] :
      ( v4_relat_1(C_207,A_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1105,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1096])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1108,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1105,c_22])).

tff(c_1111,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1108])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1115,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_18])).

tff(c_1119,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1115])).

tff(c_1460,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k7_relset_1(A_244,B_245,C_246,D_247) = k9_relat_1(C_246,D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1467,plain,(
    ! [D_247] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_247) = k9_relat_1('#skF_3',D_247) ),
    inference(resolution,[status(thm)],[c_50,c_1460])).

tff(c_93,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_143,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_152,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_282,plain,(
    ! [B_92,A_93] :
      ( k5_relat_1(B_92,k6_relat_1(A_93)) = B_92
      | ~ r1_tarski(k2_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_296,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_282])).

tff(c_452,plain,(
    ! [A_108,B_109] :
      ( k10_relat_1(A_108,k1_relat_1(B_109)) = k1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_461,plain,(
    ! [A_108,A_15] :
      ( k1_relat_1(k5_relat_1(A_108,k6_relat_1(A_15))) = k10_relat_1(A_108,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_452])).

tff(c_467,plain,(
    ! [A_113,A_114] :
      ( k1_relat_1(k5_relat_1(A_113,k6_relat_1(A_114))) = k10_relat_1(A_113,A_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_461])).

tff(c_849,plain,(
    ! [B_169,A_170] :
      ( k10_relat_1(B_169,A_170) = k1_relat_1(B_169)
      | ~ v1_relat_1(B_169)
      | ~ v5_relat_1(B_169,A_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_467])).

tff(c_870,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_152,c_849])).

tff(c_889,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_870])).

tff(c_672,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k7_relset_1(A_130,B_131,C_132,D_133) = k9_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_679,plain,(
    ! [D_133] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_133) = k9_relat_1('#skF_3',D_133) ),
    inference(resolution,[status(thm)],[c_50,c_672])).

tff(c_645,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k8_relset_1(A_123,B_124,C_125,D_126) = k10_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_652,plain,(
    ! [D_126] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_126) = k10_relat_1('#skF_3',D_126) ),
    inference(resolution,[status(thm)],[c_50,c_645])).

tff(c_326,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_335,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_326])).

tff(c_48,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_92,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_336,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_92])).

tff(c_653,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_336])).

tff(c_680,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_653])).

tff(c_899,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_680])).

tff(c_890,plain,(
    ! [D_171,B_172,C_173,A_174] :
      ( m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(B_172,C_173)))
      | ~ r1_tarski(k1_relat_1(D_171),B_172)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(k2_zfmisc_1(A_174,C_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_908,plain,(
    ! [B_175] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_175,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_175) ) ),
    inference(resolution,[status(thm)],[c_50,c_890])).

tff(c_34,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_946,plain,(
    ! [B_176] :
      ( v4_relat_1('#skF_3',B_176)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_176) ) ),
    inference(resolution,[status(thm)],[c_908,c_34])).

tff(c_951,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_946])).

tff(c_954,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_951,c_22])).

tff(c_957,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_954])).

tff(c_961,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_18])).

tff(c_965,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_961])).

tff(c_967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_899,c_965])).

tff(c_968,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1468,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_968])).

tff(c_1469,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1119,c_1468])).

tff(c_1579,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_1469])).

tff(c_1595,plain,
    ( k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_1579])).

tff(c_1597,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_979,c_1595])).

tff(c_1726,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_1597])).

tff(c_1060,plain,(
    ! [C_197,B_198,A_199] :
      ( v5_relat_1(C_197,B_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1069,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1060])).

tff(c_1139,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_1125])).

tff(c_1932,plain,(
    ! [B_312,A_313] :
      ( k10_relat_1(B_312,A_313) = k1_relat_1(B_312)
      | ~ v1_relat_1(B_312)
      | ~ v5_relat_1(B_312,A_313)
      | ~ v1_relat_1(B_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_1310])).

tff(c_1947,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1069,c_1932])).

tff(c_1968,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1947])).

tff(c_1970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_1968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/2.32  
% 4.84/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/2.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.84/2.32  
% 4.84/2.32  %Foreground sorts:
% 4.84/2.32  
% 4.84/2.32  
% 4.84/2.32  %Background operators:
% 4.84/2.32  
% 4.84/2.32  
% 4.84/2.32  %Foreground operators:
% 4.84/2.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.84/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.84/2.32  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.84/2.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.84/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.84/2.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.84/2.32  tff('#skF_2', type, '#skF_2': $i).
% 4.84/2.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.84/2.32  tff('#skF_3', type, '#skF_3': $i).
% 4.84/2.32  tff('#skF_1', type, '#skF_1': $i).
% 4.84/2.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.84/2.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.84/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/2.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.84/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/2.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.84/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/2.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.84/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/2.32  
% 5.12/2.35  tff(f_111, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 5.12/2.35  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.12/2.35  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 5.12/2.35  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.12/2.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.12/2.35  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 5.12/2.35  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.12/2.35  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.12/2.35  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.12/2.35  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.12/2.35  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.12/2.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.12/2.35  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.12/2.35  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.12/2.35  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.12/2.35  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.12/2.35  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.12/2.35  tff(c_1569, plain, (![A_255, B_256, C_257, D_258]: (k8_relset_1(A_255, B_256, C_257, D_258)=k10_relat_1(C_257, D_258) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.12/2.35  tff(c_1576, plain, (![D_258]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_258)=k10_relat_1('#skF_3', D_258))), inference(resolution, [status(thm)], [c_50, c_1569])).
% 5.12/2.35  tff(c_1717, plain, (![A_287, B_288, C_289]: (k8_relset_1(A_287, B_288, C_289, B_288)=k1_relset_1(A_287, B_288, C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.12/2.35  tff(c_1722, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1717])).
% 5.12/2.36  tff(c_1725, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1576, c_1722])).
% 5.12/2.36  tff(c_970, plain, (![C_177, A_178, B_179]: (v1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.12/2.36  tff(c_979, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_970])).
% 5.12/2.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.12/2.36  tff(c_1125, plain, (![B_210, A_211]: (k5_relat_1(B_210, k6_relat_1(A_211))=B_210 | ~r1_tarski(k2_relat_1(B_210), A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.12/2.36  tff(c_1142, plain, (![B_210]: (k5_relat_1(B_210, k6_relat_1(k2_relat_1(B_210)))=B_210 | ~v1_relat_1(B_210))), inference(resolution, [status(thm)], [c_6, c_1125])).
% 5.12/2.36  tff(c_16, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.12/2.36  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.12/2.36  tff(c_1252, plain, (![A_225, B_226]: (k10_relat_1(A_225, k1_relat_1(B_226))=k1_relat_1(k5_relat_1(A_225, B_226)) | ~v1_relat_1(B_226) | ~v1_relat_1(A_225))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.12/2.36  tff(c_1261, plain, (![A_225, A_15]: (k1_relat_1(k5_relat_1(A_225, k6_relat_1(A_15)))=k10_relat_1(A_225, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_225))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1252])).
% 5.12/2.36  tff(c_1310, plain, (![A_229, A_230]: (k1_relat_1(k5_relat_1(A_229, k6_relat_1(A_230)))=k10_relat_1(A_229, A_230) | ~v1_relat_1(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1261])).
% 5.12/2.36  tff(c_1331, plain, (![B_210]: (k10_relat_1(B_210, k2_relat_1(B_210))=k1_relat_1(B_210) | ~v1_relat_1(B_210) | ~v1_relat_1(B_210))), inference(superposition, [status(thm), theory('equality')], [c_1142, c_1310])).
% 5.12/2.36  tff(c_1096, plain, (![C_207, A_208, B_209]: (v4_relat_1(C_207, A_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.12/2.36  tff(c_1105, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_1096])).
% 5.12/2.36  tff(c_22, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.12/2.36  tff(c_1108, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1105, c_22])).
% 5.12/2.36  tff(c_1111, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1108])).
% 5.12/2.36  tff(c_18, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.12/2.36  tff(c_1115, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1111, c_18])).
% 5.12/2.36  tff(c_1119, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1115])).
% 5.12/2.36  tff(c_1460, plain, (![A_244, B_245, C_246, D_247]: (k7_relset_1(A_244, B_245, C_246, D_247)=k9_relat_1(C_246, D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.12/2.36  tff(c_1467, plain, (![D_247]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_247)=k9_relat_1('#skF_3', D_247))), inference(resolution, [status(thm)], [c_50, c_1460])).
% 5.12/2.36  tff(c_93, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.12/2.36  tff(c_102, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_93])).
% 5.12/2.36  tff(c_143, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.12/2.36  tff(c_152, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_143])).
% 5.12/2.36  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.12/2.36  tff(c_282, plain, (![B_92, A_93]: (k5_relat_1(B_92, k6_relat_1(A_93))=B_92 | ~r1_tarski(k2_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.12/2.36  tff(c_296, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_14, c_282])).
% 5.12/2.36  tff(c_452, plain, (![A_108, B_109]: (k10_relat_1(A_108, k1_relat_1(B_109))=k1_relat_1(k5_relat_1(A_108, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.12/2.36  tff(c_461, plain, (![A_108, A_15]: (k1_relat_1(k5_relat_1(A_108, k6_relat_1(A_15)))=k10_relat_1(A_108, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_24, c_452])).
% 5.12/2.36  tff(c_467, plain, (![A_113, A_114]: (k1_relat_1(k5_relat_1(A_113, k6_relat_1(A_114)))=k10_relat_1(A_113, A_114) | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_461])).
% 5.12/2.36  tff(c_849, plain, (![B_169, A_170]: (k10_relat_1(B_169, A_170)=k1_relat_1(B_169) | ~v1_relat_1(B_169) | ~v5_relat_1(B_169, A_170) | ~v1_relat_1(B_169))), inference(superposition, [status(thm), theory('equality')], [c_296, c_467])).
% 5.12/2.36  tff(c_870, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_152, c_849])).
% 5.12/2.36  tff(c_889, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_870])).
% 5.12/2.36  tff(c_672, plain, (![A_130, B_131, C_132, D_133]: (k7_relset_1(A_130, B_131, C_132, D_133)=k9_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.12/2.36  tff(c_679, plain, (![D_133]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_133)=k9_relat_1('#skF_3', D_133))), inference(resolution, [status(thm)], [c_50, c_672])).
% 5.12/2.36  tff(c_645, plain, (![A_123, B_124, C_125, D_126]: (k8_relset_1(A_123, B_124, C_125, D_126)=k10_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.12/2.36  tff(c_652, plain, (![D_126]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_126)=k10_relat_1('#skF_3', D_126))), inference(resolution, [status(thm)], [c_50, c_645])).
% 5.12/2.36  tff(c_326, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.12/2.36  tff(c_335, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_326])).
% 5.12/2.36  tff(c_48, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.12/2.36  tff(c_92, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 5.12/2.36  tff(c_336, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_92])).
% 5.12/2.36  tff(c_653, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_336])).
% 5.12/2.36  tff(c_680, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_679, c_653])).
% 5.12/2.36  tff(c_899, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_889, c_680])).
% 5.12/2.36  tff(c_890, plain, (![D_171, B_172, C_173, A_174]: (m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(B_172, C_173))) | ~r1_tarski(k1_relat_1(D_171), B_172) | ~m1_subset_1(D_171, k1_zfmisc_1(k2_zfmisc_1(A_174, C_173))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.12/2.36  tff(c_908, plain, (![B_175]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_175, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_175))), inference(resolution, [status(thm)], [c_50, c_890])).
% 5.12/2.36  tff(c_34, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.12/2.36  tff(c_946, plain, (![B_176]: (v4_relat_1('#skF_3', B_176) | ~r1_tarski(k1_relat_1('#skF_3'), B_176))), inference(resolution, [status(thm)], [c_908, c_34])).
% 5.12/2.36  tff(c_951, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_946])).
% 5.12/2.36  tff(c_954, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_951, c_22])).
% 5.12/2.36  tff(c_957, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_954])).
% 5.12/2.36  tff(c_961, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_957, c_18])).
% 5.12/2.36  tff(c_965, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_961])).
% 5.12/2.36  tff(c_967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_899, c_965])).
% 5.12/2.36  tff(c_968, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 5.12/2.36  tff(c_1468, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_968])).
% 5.12/2.36  tff(c_1469, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1119, c_1468])).
% 5.12/2.36  tff(c_1579, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1576, c_1469])).
% 5.12/2.36  tff(c_1595, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1331, c_1579])).
% 5.12/2.36  tff(c_1597, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_979, c_979, c_1595])).
% 5.12/2.36  tff(c_1726, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_1597])).
% 5.12/2.36  tff(c_1060, plain, (![C_197, B_198, A_199]: (v5_relat_1(C_197, B_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.12/2.36  tff(c_1069, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1060])).
% 5.12/2.36  tff(c_1139, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_14, c_1125])).
% 5.12/2.36  tff(c_1932, plain, (![B_312, A_313]: (k10_relat_1(B_312, A_313)=k1_relat_1(B_312) | ~v1_relat_1(B_312) | ~v5_relat_1(B_312, A_313) | ~v1_relat_1(B_312))), inference(superposition, [status(thm), theory('equality')], [c_1139, c_1310])).
% 5.12/2.36  tff(c_1947, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1069, c_1932])).
% 5.12/2.36  tff(c_1968, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1947])).
% 5.12/2.36  tff(c_1970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1726, c_1968])).
% 5.12/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.12/2.36  
% 5.12/2.36  Inference rules
% 5.12/2.36  ----------------------
% 5.12/2.36  #Ref     : 0
% 5.12/2.36  #Sup     : 395
% 5.12/2.36  #Fact    : 0
% 5.12/2.36  #Define  : 0
% 5.12/2.36  #Split   : 4
% 5.12/2.36  #Chain   : 0
% 5.12/2.36  #Close   : 0
% 5.12/2.36  
% 5.12/2.36  Ordering : KBO
% 5.12/2.36  
% 5.12/2.36  Simplification rules
% 5.12/2.36  ----------------------
% 5.12/2.36  #Subsume      : 16
% 5.12/2.36  #Demod        : 286
% 5.12/2.36  #Tautology    : 196
% 5.12/2.36  #SimpNegUnit  : 2
% 5.12/2.36  #BackRed      : 12
% 5.12/2.36  
% 5.12/2.36  #Partial instantiations: 0
% 5.12/2.36  #Strategies tried      : 1
% 5.12/2.36  
% 5.12/2.36  Timing (in seconds)
% 5.12/2.36  ----------------------
% 5.17/2.36  Preprocessing        : 0.52
% 5.17/2.36  Parsing              : 0.27
% 5.17/2.36  CNF conversion       : 0.03
% 5.17/2.36  Main loop            : 0.91
% 5.17/2.36  Inferencing          : 0.36
% 5.17/2.36  Reduction            : 0.30
% 5.17/2.36  Demodulation         : 0.22
% 5.17/2.36  BG Simplification    : 0.04
% 5.17/2.36  Subsumption          : 0.14
% 5.17/2.36  Abstraction          : 0.05
% 5.17/2.36  MUC search           : 0.00
% 5.17/2.36  Cooper               : 0.00
% 5.17/2.36  Total                : 1.50
% 5.17/2.36  Index Insertion      : 0.00
% 5.17/2.36  Index Deletion       : 0.00
% 5.17/2.36  Index Matching       : 0.00
% 5.17/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
