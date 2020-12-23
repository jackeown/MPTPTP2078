%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:56 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 168 expanded)
%              Number of leaves         :   40 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 276 expanded)
%              Number of equality atoms :   63 ( 108 expanded)
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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_796,plain,(
    ! [B_139,A_140] :
      ( k5_relat_1(B_139,k6_relat_1(A_140)) = B_139
      | ~ r1_tarski(k2_relat_1(B_139),A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_813,plain,(
    ! [B_139] :
      ( k5_relat_1(B_139,k6_relat_1(k2_relat_1(B_139))) = B_139
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_796])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_920,plain,(
    ! [A_147,B_148] :
      ( k10_relat_1(A_147,k1_relat_1(B_148)) = k1_relat_1(k5_relat_1(A_147,B_148))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_929,plain,(
    ! [A_147,A_13] :
      ( k1_relat_1(k5_relat_1(A_147,k6_relat_1(A_13))) = k10_relat_1(A_147,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_920])).

tff(c_934,plain,(
    ! [A_149,A_150] :
      ( k1_relat_1(k5_relat_1(A_149,k6_relat_1(A_150))) = k10_relat_1(A_149,A_150)
      | ~ v1_relat_1(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_929])).

tff(c_955,plain,(
    ! [B_139] :
      ( k10_relat_1(B_139,k2_relat_1(B_139)) = k1_relat_1(B_139)
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_934])).

tff(c_1185,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k8_relset_1(A_171,B_172,C_173,D_174) = k10_relat_1(C_173,D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1188,plain,(
    ! [D_174] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_174) = k10_relat_1('#skF_3',D_174) ),
    inference(resolution,[status(thm)],[c_44,c_1185])).

tff(c_701,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_705,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_701])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_708,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_705,c_18])).

tff(c_711,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_708])).

tff(c_735,plain,(
    ! [B_133,A_134] :
      ( k2_relat_1(k7_relat_1(B_133,A_134)) = k9_relat_1(B_133,A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_750,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_735])).

tff(c_754,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_750])).

tff(c_1140,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k7_relset_1(A_164,B_165,C_166,D_167) = k9_relat_1(C_166,D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1143,plain,(
    ! [D_167] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_167) = k9_relat_1('#skF_3',D_167) ),
    inference(resolution,[status(thm)],[c_44,c_1140])).

tff(c_1110,plain,(
    ! [A_159,B_160,C_161] :
      ( k1_relset_1(A_159,B_160,C_161) = k1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1114,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1110])).

tff(c_473,plain,(
    ! [D_101,B_102,C_103,A_104] :
      ( m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(B_102,C_103)))
      | ~ r1_tarski(k1_relat_1(D_101),B_102)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_104,C_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_477,plain,(
    ! [B_105] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_105,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_105) ) ),
    inference(resolution,[status(thm)],[c_44,c_473])).

tff(c_30,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_509,plain,(
    ! [B_106] :
      ( v4_relat_1('#skF_3',B_106)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_106) ) ),
    inference(resolution,[status(thm)],[c_477,c_30])).

tff(c_514,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_509])).

tff(c_517,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_514,c_18])).

tff(c_520,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_517])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_530,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_14])).

tff(c_534,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_530])).

tff(c_78,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_82,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    ! [B_69,A_70] :
      ( k5_relat_1(B_69,k6_relat_1(A_70)) = B_69
      | ~ r1_tarski(k2_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_190,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_319,plain,(
    ! [A_83,B_84] :
      ( k10_relat_1(A_83,k1_relat_1(B_84)) = k1_relat_1(k5_relat_1(A_83,B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_328,plain,(
    ! [A_83,A_13] :
      ( k1_relat_1(k5_relat_1(A_83,k6_relat_1(A_13))) = k10_relat_1(A_83,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_319])).

tff(c_347,plain,(
    ! [A_90,A_91] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_91))) = k10_relat_1(A_90,A_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_328])).

tff(c_671,plain,(
    ! [B_120,A_121] :
      ( k10_relat_1(B_120,A_121) = k1_relat_1(B_120)
      | ~ v1_relat_1(B_120)
      | ~ v5_relat_1(B_120,A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_347])).

tff(c_683,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_671])).

tff(c_693,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_683])).

tff(c_375,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_378,plain,(
    ! [D_95] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_95) = k9_relat_1('#skF_3',D_95) ),
    inference(resolution,[status(thm)],[c_44,c_375])).

tff(c_333,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k8_relset_1(A_85,B_86,C_87,D_88) = k10_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_336,plain,(
    ! [D_88] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_88) = k10_relat_1('#skF_3',D_88) ),
    inference(resolution,[status(thm)],[c_44,c_333])).

tff(c_229,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_233,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_229])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_234,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_83])).

tff(c_337,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_234])).

tff(c_400,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_337])).

tff(c_694,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_400])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_694])).

tff(c_698,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1115,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_698])).

tff(c_1144,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1115])).

tff(c_1145,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_1144])).

tff(c_1190,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1145])).

tff(c_1203,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_1190])).

tff(c_1207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.61  
% 2.89/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.61  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.61  
% 2.89/1.61  %Foreground sorts:
% 2.89/1.61  
% 2.89/1.61  
% 2.89/1.61  %Background operators:
% 2.89/1.61  
% 2.89/1.61  
% 2.89/1.61  %Foreground operators:
% 2.89/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.89/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.89/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.89/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.89/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.89/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.89/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.61  
% 3.23/1.63  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.23/1.63  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.23/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.23/1.63  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.23/1.63  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.23/1.63  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.23/1.63  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.23/1.63  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.23/1.63  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.23/1.63  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.23/1.63  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.23/1.63  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.23/1.63  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.23/1.63  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.23/1.63  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.23/1.63  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.23/1.63  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.63  tff(c_66, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.23/1.63  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.23/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.63  tff(c_796, plain, (![B_139, A_140]: (k5_relat_1(B_139, k6_relat_1(A_140))=B_139 | ~r1_tarski(k2_relat_1(B_139), A_140) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.23/1.63  tff(c_813, plain, (![B_139]: (k5_relat_1(B_139, k6_relat_1(k2_relat_1(B_139)))=B_139 | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_6, c_796])).
% 3.23/1.63  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.23/1.63  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/1.63  tff(c_920, plain, (![A_147, B_148]: (k10_relat_1(A_147, k1_relat_1(B_148))=k1_relat_1(k5_relat_1(A_147, B_148)) | ~v1_relat_1(B_148) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.63  tff(c_929, plain, (![A_147, A_13]: (k1_relat_1(k5_relat_1(A_147, k6_relat_1(A_13)))=k10_relat_1(A_147, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_20, c_920])).
% 3.23/1.63  tff(c_934, plain, (![A_149, A_150]: (k1_relat_1(k5_relat_1(A_149, k6_relat_1(A_150)))=k10_relat_1(A_149, A_150) | ~v1_relat_1(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_929])).
% 3.23/1.63  tff(c_955, plain, (![B_139]: (k10_relat_1(B_139, k2_relat_1(B_139))=k1_relat_1(B_139) | ~v1_relat_1(B_139) | ~v1_relat_1(B_139))), inference(superposition, [status(thm), theory('equality')], [c_813, c_934])).
% 3.23/1.63  tff(c_1185, plain, (![A_171, B_172, C_173, D_174]: (k8_relset_1(A_171, B_172, C_173, D_174)=k10_relat_1(C_173, D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.63  tff(c_1188, plain, (![D_174]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_174)=k10_relat_1('#skF_3', D_174))), inference(resolution, [status(thm)], [c_44, c_1185])).
% 3.23/1.63  tff(c_701, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.63  tff(c_705, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_701])).
% 3.23/1.63  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.23/1.63  tff(c_708, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_705, c_18])).
% 3.23/1.63  tff(c_711, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_708])).
% 3.23/1.63  tff(c_735, plain, (![B_133, A_134]: (k2_relat_1(k7_relat_1(B_133, A_134))=k9_relat_1(B_133, A_134) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.63  tff(c_750, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_711, c_735])).
% 3.23/1.63  tff(c_754, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_750])).
% 3.23/1.63  tff(c_1140, plain, (![A_164, B_165, C_166, D_167]: (k7_relset_1(A_164, B_165, C_166, D_167)=k9_relat_1(C_166, D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.23/1.63  tff(c_1143, plain, (![D_167]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_167)=k9_relat_1('#skF_3', D_167))), inference(resolution, [status(thm)], [c_44, c_1140])).
% 3.23/1.63  tff(c_1110, plain, (![A_159, B_160, C_161]: (k1_relset_1(A_159, B_160, C_161)=k1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.23/1.63  tff(c_1114, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1110])).
% 3.23/1.63  tff(c_473, plain, (![D_101, B_102, C_103, A_104]: (m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(B_102, C_103))) | ~r1_tarski(k1_relat_1(D_101), B_102) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_104, C_103))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.63  tff(c_477, plain, (![B_105]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_105, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_105))), inference(resolution, [status(thm)], [c_44, c_473])).
% 3.23/1.63  tff(c_30, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.63  tff(c_509, plain, (![B_106]: (v4_relat_1('#skF_3', B_106) | ~r1_tarski(k1_relat_1('#skF_3'), B_106))), inference(resolution, [status(thm)], [c_477, c_30])).
% 3.23/1.63  tff(c_514, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_509])).
% 3.23/1.63  tff(c_517, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_514, c_18])).
% 3.23/1.63  tff(c_520, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_517])).
% 3.23/1.63  tff(c_14, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.23/1.63  tff(c_530, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_520, c_14])).
% 3.23/1.63  tff(c_534, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_530])).
% 3.23/1.63  tff(c_78, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.23/1.63  tff(c_82, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_78])).
% 3.23/1.63  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.63  tff(c_176, plain, (![B_69, A_70]: (k5_relat_1(B_69, k6_relat_1(A_70))=B_69 | ~r1_tarski(k2_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.23/1.63  tff(c_190, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_176])).
% 3.23/1.63  tff(c_319, plain, (![A_83, B_84]: (k10_relat_1(A_83, k1_relat_1(B_84))=k1_relat_1(k5_relat_1(A_83, B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.23/1.63  tff(c_328, plain, (![A_83, A_13]: (k1_relat_1(k5_relat_1(A_83, k6_relat_1(A_13)))=k10_relat_1(A_83, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_20, c_319])).
% 3.23/1.63  tff(c_347, plain, (![A_90, A_91]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_91)))=k10_relat_1(A_90, A_91) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_328])).
% 3.23/1.63  tff(c_671, plain, (![B_120, A_121]: (k10_relat_1(B_120, A_121)=k1_relat_1(B_120) | ~v1_relat_1(B_120) | ~v5_relat_1(B_120, A_121) | ~v1_relat_1(B_120))), inference(superposition, [status(thm), theory('equality')], [c_190, c_347])).
% 3.23/1.63  tff(c_683, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_671])).
% 3.23/1.63  tff(c_693, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_683])).
% 3.23/1.63  tff(c_375, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.23/1.63  tff(c_378, plain, (![D_95]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_95)=k9_relat_1('#skF_3', D_95))), inference(resolution, [status(thm)], [c_44, c_375])).
% 3.23/1.63  tff(c_333, plain, (![A_85, B_86, C_87, D_88]: (k8_relset_1(A_85, B_86, C_87, D_88)=k10_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.63  tff(c_336, plain, (![D_88]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_88)=k10_relat_1('#skF_3', D_88))), inference(resolution, [status(thm)], [c_44, c_333])).
% 3.23/1.63  tff(c_229, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.63  tff(c_233, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_229])).
% 3.23/1.63  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.23/1.63  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.23/1.63  tff(c_234, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_83])).
% 3.23/1.63  tff(c_337, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_234])).
% 3.23/1.63  tff(c_400, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_337])).
% 3.23/1.63  tff(c_694, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_400])).
% 3.23/1.63  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_694])).
% 3.23/1.63  tff(c_698, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.23/1.63  tff(c_1115, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_698])).
% 3.23/1.63  tff(c_1144, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1115])).
% 3.23/1.63  tff(c_1145, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_1144])).
% 3.23/1.63  tff(c_1190, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1145])).
% 3.23/1.63  tff(c_1203, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_955, c_1190])).
% 3.23/1.63  tff(c_1207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1203])).
% 3.23/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.63  
% 3.23/1.63  Inference rules
% 3.23/1.63  ----------------------
% 3.23/1.63  #Ref     : 0
% 3.23/1.63  #Sup     : 250
% 3.23/1.63  #Fact    : 0
% 3.23/1.63  #Define  : 0
% 3.23/1.63  #Split   : 1
% 3.23/1.63  #Chain   : 0
% 3.23/1.63  #Close   : 0
% 3.23/1.63  
% 3.23/1.63  Ordering : KBO
% 3.23/1.63  
% 3.23/1.63  Simplification rules
% 3.23/1.63  ----------------------
% 3.23/1.63  #Subsume      : 7
% 3.23/1.63  #Demod        : 189
% 3.23/1.63  #Tautology    : 150
% 3.23/1.63  #SimpNegUnit  : 0
% 3.23/1.63  #BackRed      : 10
% 3.23/1.63  
% 3.23/1.63  #Partial instantiations: 0
% 3.23/1.63  #Strategies tried      : 1
% 3.23/1.63  
% 3.23/1.63  Timing (in seconds)
% 3.23/1.63  ----------------------
% 3.23/1.64  Preprocessing        : 0.36
% 3.23/1.64  Parsing              : 0.19
% 3.23/1.64  CNF conversion       : 0.02
% 3.23/1.64  Main loop            : 0.38
% 3.23/1.64  Inferencing          : 0.15
% 3.23/1.64  Reduction            : 0.12
% 3.23/1.64  Demodulation         : 0.09
% 3.23/1.64  BG Simplification    : 0.02
% 3.23/1.64  Subsumption          : 0.05
% 3.23/1.64  Abstraction          : 0.02
% 3.23/1.64  MUC search           : 0.00
% 3.23/1.64  Cooper               : 0.00
% 3.23/1.64  Total                : 0.78
% 3.23/1.64  Index Insertion      : 0.00
% 3.23/1.64  Index Deletion       : 0.00
% 3.23/1.64  Index Matching       : 0.00
% 3.23/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
