%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:55 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 162 expanded)
%              Number of leaves         :   40 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 273 expanded)
%              Number of equality atoms :   60 ( 103 expanded)
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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_70,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_37,axiom,(
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

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_985,plain,(
    ! [B_154,A_155] :
      ( k5_relat_1(B_154,k6_relat_1(A_155)) = B_154
      | ~ r1_tarski(k2_relat_1(B_154),A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1002,plain,(
    ! [B_154] :
      ( k5_relat_1(B_154,k6_relat_1(k2_relat_1(B_154))) = B_154
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_6,c_985])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1128,plain,(
    ! [A_168,B_169] :
      ( k10_relat_1(A_168,k1_relat_1(B_169)) = k1_relat_1(k5_relat_1(A_168,B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1137,plain,(
    ! [A_168,A_13] :
      ( k1_relat_1(k5_relat_1(A_168,k6_relat_1(A_13))) = k10_relat_1(A_168,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1128])).

tff(c_1147,plain,(
    ! [A_170,A_171] :
      ( k1_relat_1(k5_relat_1(A_170,k6_relat_1(A_171))) = k10_relat_1(A_170,A_171)
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1137])).

tff(c_1168,plain,(
    ! [B_154] :
      ( k10_relat_1(B_154,k2_relat_1(B_154)) = k1_relat_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_1147])).

tff(c_961,plain,(
    ! [C_151,A_152,B_153] :
      ( v4_relat_1(C_151,A_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_965,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_961])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_968,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_965,c_18])).

tff(c_971,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_968])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_975,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_14])).

tff(c_979,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_975])).

tff(c_1352,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k7_relset_1(A_184,B_185,C_186,D_187) = k9_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1355,plain,(
    ! [D_187] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_187) = k9_relat_1('#skF_3',D_187) ),
    inference(resolution,[status(thm)],[c_44,c_1352])).

tff(c_1333,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k8_relset_1(A_179,B_180,C_181,D_182) = k10_relat_1(C_181,D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1336,plain,(
    ! [D_182] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_182) = k10_relat_1('#skF_3',D_182) ),
    inference(resolution,[status(thm)],[c_44,c_1333])).

tff(c_1113,plain,(
    ! [A_162,B_163,C_164] :
      ( k1_relset_1(A_162,B_163,C_164) = k1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1117,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1113])).

tff(c_473,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ r1_tarski(k2_relat_1(C_100),B_102)
      | ~ r1_tarski(k1_relat_1(C_100),A_101)
      | ~ v1_relat_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_570,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ r1_tarski(k2_relat_1(C_106),B_108)
      | ~ r1_tarski(k1_relat_1(C_106),A_107)
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_473,c_30])).

tff(c_602,plain,(
    ! [C_111,A_112] :
      ( v4_relat_1(C_111,A_112)
      | ~ r1_tarski(k1_relat_1(C_111),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_570])).

tff(c_619,plain,(
    ! [C_113] :
      ( v4_relat_1(C_113,k1_relat_1(C_113))
      | ~ v1_relat_1(C_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_602])).

tff(c_696,plain,(
    ! [C_123] :
      ( k7_relat_1(C_123,k1_relat_1(C_123)) = C_123
      | ~ v1_relat_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_619,c_18])).

tff(c_705,plain,(
    ! [C_123] :
      ( k9_relat_1(C_123,k1_relat_1(C_123)) = k2_relat_1(C_123)
      | ~ v1_relat_1(C_123)
      | ~ v1_relat_1(C_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_14])).

tff(c_78,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
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
    ! [B_68,A_69] :
      ( k5_relat_1(B_68,k6_relat_1(A_69)) = B_68
      | ~ r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_190,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_176])).

tff(c_319,plain,(
    ! [A_82,B_83] :
      ( k10_relat_1(A_82,k1_relat_1(B_83)) = k1_relat_1(k5_relat_1(A_82,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_328,plain,(
    ! [A_82,A_13] :
      ( k1_relat_1(k5_relat_1(A_82,k6_relat_1(A_13))) = k10_relat_1(A_82,A_13)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_319])).

tff(c_347,plain,(
    ! [A_89,A_90] :
      ( k1_relat_1(k5_relat_1(A_89,k6_relat_1(A_90))) = k10_relat_1(A_89,A_90)
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_328])).

tff(c_846,plain,(
    ! [B_135,A_136] :
      ( k10_relat_1(B_135,A_136) = k1_relat_1(B_135)
      | ~ v1_relat_1(B_135)
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_347])).

tff(c_864,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_846])).

tff(c_878,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_864])).

tff(c_375,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k7_relset_1(A_91,B_92,C_93,D_94) = k9_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_378,plain,(
    ! [D_94] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_94) = k9_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_44,c_375])).

tff(c_333,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( k8_relset_1(A_84,B_85,C_86,D_87) = k10_relat_1(C_86,D_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_336,plain,(
    ! [D_87] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_87) = k10_relat_1('#skF_3',D_87) ),
    inference(resolution,[status(thm)],[c_44,c_333])).

tff(c_229,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_233,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_229])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

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

tff(c_879,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_400])).

tff(c_886,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_879])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_886])).

tff(c_891,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1118,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_891])).

tff(c_1338,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1118])).

tff(c_1356,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1355,c_1338])).

tff(c_1357,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1356])).

tff(c_1375,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_1357])).

tff(c_1379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.46  
% 3.02/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.46  
% 3.17/1.46  %Foreground sorts:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Background operators:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Foreground operators:
% 3.17/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.17/1.46  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.17/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.17/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.46  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.17/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.17/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.46  
% 3.17/1.48  tff(f_107, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.17/1.48  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.17/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.48  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.17/1.48  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.17/1.48  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.17/1.48  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.17/1.48  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.17/1.48  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.17/1.48  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.17/1.48  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.17/1.48  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.17/1.48  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.17/1.48  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.17/1.48  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.17/1.48  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.17/1.48  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.48  tff(c_66, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.48  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.17/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.48  tff(c_985, plain, (![B_154, A_155]: (k5_relat_1(B_154, k6_relat_1(A_155))=B_154 | ~r1_tarski(k2_relat_1(B_154), A_155) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.48  tff(c_1002, plain, (![B_154]: (k5_relat_1(B_154, k6_relat_1(k2_relat_1(B_154)))=B_154 | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_6, c_985])).
% 3.17/1.48  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.48  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.17/1.48  tff(c_1128, plain, (![A_168, B_169]: (k10_relat_1(A_168, k1_relat_1(B_169))=k1_relat_1(k5_relat_1(A_168, B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.48  tff(c_1137, plain, (![A_168, A_13]: (k1_relat_1(k5_relat_1(A_168, k6_relat_1(A_13)))=k10_relat_1(A_168, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_168))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1128])).
% 3.17/1.48  tff(c_1147, plain, (![A_170, A_171]: (k1_relat_1(k5_relat_1(A_170, k6_relat_1(A_171)))=k10_relat_1(A_170, A_171) | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1137])).
% 3.17/1.48  tff(c_1168, plain, (![B_154]: (k10_relat_1(B_154, k2_relat_1(B_154))=k1_relat_1(B_154) | ~v1_relat_1(B_154) | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_1147])).
% 3.17/1.48  tff(c_961, plain, (![C_151, A_152, B_153]: (v4_relat_1(C_151, A_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.17/1.48  tff(c_965, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_961])).
% 3.17/1.48  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.48  tff(c_968, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_965, c_18])).
% 3.17/1.48  tff(c_971, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_968])).
% 3.17/1.48  tff(c_14, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.48  tff(c_975, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_971, c_14])).
% 3.17/1.48  tff(c_979, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_975])).
% 3.17/1.48  tff(c_1352, plain, (![A_184, B_185, C_186, D_187]: (k7_relset_1(A_184, B_185, C_186, D_187)=k9_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.17/1.48  tff(c_1355, plain, (![D_187]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_187)=k9_relat_1('#skF_3', D_187))), inference(resolution, [status(thm)], [c_44, c_1352])).
% 3.17/1.48  tff(c_1333, plain, (![A_179, B_180, C_181, D_182]: (k8_relset_1(A_179, B_180, C_181, D_182)=k10_relat_1(C_181, D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.48  tff(c_1336, plain, (![D_182]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_182)=k10_relat_1('#skF_3', D_182))), inference(resolution, [status(thm)], [c_44, c_1333])).
% 3.17/1.48  tff(c_1113, plain, (![A_162, B_163, C_164]: (k1_relset_1(A_162, B_163, C_164)=k1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.17/1.48  tff(c_1117, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1113])).
% 3.17/1.48  tff(c_473, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~r1_tarski(k2_relat_1(C_100), B_102) | ~r1_tarski(k1_relat_1(C_100), A_101) | ~v1_relat_1(C_100))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.17/1.48  tff(c_30, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.17/1.48  tff(c_570, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~r1_tarski(k2_relat_1(C_106), B_108) | ~r1_tarski(k1_relat_1(C_106), A_107) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_473, c_30])).
% 3.17/1.48  tff(c_602, plain, (![C_111, A_112]: (v4_relat_1(C_111, A_112) | ~r1_tarski(k1_relat_1(C_111), A_112) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_6, c_570])).
% 3.17/1.48  tff(c_619, plain, (![C_113]: (v4_relat_1(C_113, k1_relat_1(C_113)) | ~v1_relat_1(C_113))), inference(resolution, [status(thm)], [c_6, c_602])).
% 3.17/1.48  tff(c_696, plain, (![C_123]: (k7_relat_1(C_123, k1_relat_1(C_123))=C_123 | ~v1_relat_1(C_123))), inference(resolution, [status(thm)], [c_619, c_18])).
% 3.17/1.48  tff(c_705, plain, (![C_123]: (k9_relat_1(C_123, k1_relat_1(C_123))=k2_relat_1(C_123) | ~v1_relat_1(C_123) | ~v1_relat_1(C_123))), inference(superposition, [status(thm), theory('equality')], [c_696, c_14])).
% 3.17/1.48  tff(c_78, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.17/1.48  tff(c_82, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_78])).
% 3.17/1.48  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.48  tff(c_176, plain, (![B_68, A_69]: (k5_relat_1(B_68, k6_relat_1(A_69))=B_68 | ~r1_tarski(k2_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.48  tff(c_190, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_176])).
% 3.17/1.48  tff(c_319, plain, (![A_82, B_83]: (k10_relat_1(A_82, k1_relat_1(B_83))=k1_relat_1(k5_relat_1(A_82, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.17/1.48  tff(c_328, plain, (![A_82, A_13]: (k1_relat_1(k5_relat_1(A_82, k6_relat_1(A_13)))=k10_relat_1(A_82, A_13) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_20, c_319])).
% 3.17/1.48  tff(c_347, plain, (![A_89, A_90]: (k1_relat_1(k5_relat_1(A_89, k6_relat_1(A_90)))=k10_relat_1(A_89, A_90) | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_328])).
% 3.17/1.48  tff(c_846, plain, (![B_135, A_136]: (k10_relat_1(B_135, A_136)=k1_relat_1(B_135) | ~v1_relat_1(B_135) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_190, c_347])).
% 3.17/1.48  tff(c_864, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_846])).
% 3.17/1.48  tff(c_878, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_864])).
% 3.17/1.48  tff(c_375, plain, (![A_91, B_92, C_93, D_94]: (k7_relset_1(A_91, B_92, C_93, D_94)=k9_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.17/1.48  tff(c_378, plain, (![D_94]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_94)=k9_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_44, c_375])).
% 3.17/1.48  tff(c_333, plain, (![A_84, B_85, C_86, D_87]: (k8_relset_1(A_84, B_85, C_86, D_87)=k10_relat_1(C_86, D_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.48  tff(c_336, plain, (![D_87]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_87)=k10_relat_1('#skF_3', D_87))), inference(resolution, [status(thm)], [c_44, c_333])).
% 3.17/1.48  tff(c_229, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.17/1.48  tff(c_233, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_229])).
% 3.17/1.48  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.17/1.48  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.17/1.48  tff(c_234, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_83])).
% 3.17/1.48  tff(c_337, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_234])).
% 3.17/1.48  tff(c_400, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_337])).
% 3.17/1.48  tff(c_879, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_400])).
% 3.17/1.48  tff(c_886, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_705, c_879])).
% 3.17/1.48  tff(c_890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_886])).
% 3.17/1.48  tff(c_891, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.17/1.48  tff(c_1118, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1117, c_891])).
% 3.17/1.48  tff(c_1338, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_1118])).
% 3.17/1.48  tff(c_1356, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1355, c_1338])).
% 3.17/1.48  tff(c_1357, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1356])).
% 3.17/1.48  tff(c_1375, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1168, c_1357])).
% 3.17/1.48  tff(c_1379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1375])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 286
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 1
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 9
% 3.17/1.48  #Demod        : 228
% 3.17/1.48  #Tautology    : 161
% 3.17/1.48  #SimpNegUnit  : 0
% 3.17/1.48  #BackRed      : 9
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.49  Preprocessing        : 0.31
% 3.17/1.49  Parsing              : 0.17
% 3.17/1.49  CNF conversion       : 0.02
% 3.17/1.49  Main loop            : 0.40
% 3.17/1.49  Inferencing          : 0.16
% 3.17/1.49  Reduction            : 0.13
% 3.17/1.49  Demodulation         : 0.09
% 3.17/1.49  BG Simplification    : 0.02
% 3.17/1.49  Subsumption          : 0.06
% 3.17/1.49  Abstraction          : 0.02
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.75
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
