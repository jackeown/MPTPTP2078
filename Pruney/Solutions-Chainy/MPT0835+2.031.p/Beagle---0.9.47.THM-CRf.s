%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:00 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 252 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 445 expanded)
%              Number of equality atoms :   62 ( 135 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_46,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_92,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_92])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_654,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_658,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_654])).

tff(c_693,plain,(
    ! [B_123,A_124] :
      ( k7_relat_1(B_123,A_124) = B_123
      | ~ v4_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_696,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_658,c_693])).

tff(c_699,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_696])).

tff(c_709,plain,(
    ! [B_127,A_128] :
      ( k2_relat_1(k7_relat_1(B_127,A_128)) = k9_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_727,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_709])).

tff(c_731,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_727])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_659,plain,(
    ! [B_119,A_120] :
      ( v5_relat_1(B_119,A_120)
      | ~ r1_tarski(k2_relat_1(B_119),A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_673,plain,(
    ! [B_119] :
      ( v5_relat_1(B_119,k2_relat_1(B_119))
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_659])).

tff(c_1228,plain,(
    ! [B_168,A_169] :
      ( v5_relat_1(k7_relat_1(B_168,A_169),k9_relat_1(B_168,A_169))
      | ~ v1_relat_1(k7_relat_1(B_168,A_169))
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_673])).

tff(c_1240,plain,
    ( v5_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_1228])).

tff(c_1253,plain,(
    v5_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_98,c_699,c_731,c_1240])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_741,plain,(
    ! [B_132,A_133] :
      ( k5_relat_1(B_132,k6_relat_1(A_133)) = B_132
      | ~ r1_tarski(k2_relat_1(B_132),A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_755,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_741])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_776,plain,(
    ! [A_135,B_136] :
      ( k10_relat_1(A_135,k1_relat_1(B_136)) = k1_relat_1(k5_relat_1(A_135,B_136))
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_785,plain,(
    ! [A_135,A_19] :
      ( k1_relat_1(k5_relat_1(A_135,k6_relat_1(A_19))) = k10_relat_1(A_135,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_776])).

tff(c_889,plain,(
    ! [A_145,A_146] :
      ( k1_relat_1(k5_relat_1(A_145,k6_relat_1(A_146))) = k10_relat_1(A_145,A_146)
      | ~ v1_relat_1(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_785])).

tff(c_907,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(B_7,A_6) = k1_relat_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_889])).

tff(c_1258,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1253,c_907])).

tff(c_1261,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1258])).

tff(c_1263,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k8_relset_1(A_170,B_171,C_172,D_173) = k10_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1266,plain,(
    ! [D_173] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_173) = k10_relat_1('#skF_3',D_173) ),
    inference(resolution,[status(thm)],[c_46,c_1263])).

tff(c_1137,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k7_relset_1(A_161,B_162,C_163,D_164) = k9_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1140,plain,(
    ! [D_164] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_164) = k9_relat_1('#skF_3',D_164) ),
    inference(resolution,[status(thm)],[c_46,c_1137])).

tff(c_879,plain,(
    ! [A_142,B_143,C_144] :
      ( k1_relset_1(A_142,B_143,C_144) = k1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_883,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_879])).

tff(c_18,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_138,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_134])).

tff(c_193,plain,(
    ! [B_68,A_69] :
      ( k5_relat_1(B_68,k6_relat_1(A_69)) = B_68
      | ~ r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_207,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_239,plain,(
    ! [A_74,B_75] :
      ( k10_relat_1(A_74,k1_relat_1(B_75)) = k1_relat_1(k5_relat_1(A_74,B_75))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_248,plain,(
    ! [A_74,A_19] :
      ( k1_relat_1(k5_relat_1(A_74,k6_relat_1(A_19))) = k10_relat_1(A_74,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_342,plain,(
    ! [A_81,A_82] :
      ( k1_relat_1(k5_relat_1(A_81,k6_relat_1(A_82))) = k10_relat_1(A_81,A_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_248])).

tff(c_596,plain,(
    ! [B_108,A_109] :
      ( k10_relat_1(B_108,A_109) = k1_relat_1(B_108)
      | ~ v1_relat_1(B_108)
      | ~ v5_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_342])).

tff(c_608,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_596])).

tff(c_618,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_608])).

tff(c_582,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k8_relset_1(A_103,B_104,C_105,D_106) = k10_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_585,plain,(
    ! [D_106] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_106) = k10_relat_1('#skF_3',D_106) ),
    inference(resolution,[status(thm)],[c_46,c_582])).

tff(c_549,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_relset_1(A_96,B_97,C_98,D_99) = k9_relat_1(C_98,D_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_552,plain,(
    ! [D_99] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_99) = k9_relat_1('#skF_3',D_99) ),
    inference(resolution,[status(thm)],[c_46,c_549])).

tff(c_466,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_470,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_466])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_99,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_471,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_99])).

tff(c_553,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_471])).

tff(c_586,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_553])).

tff(c_619,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_586])).

tff(c_626,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_619])).

tff(c_630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_626])).

tff(c_631,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_884,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_631])).

tff(c_1141,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_884])).

tff(c_1142,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_1141])).

tff(c_1284,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1142])).

tff(c_1289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_1284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.54  
% 3.27/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.54  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.27/1.54  
% 3.27/1.54  %Foreground sorts:
% 3.27/1.54  
% 3.27/1.54  
% 3.27/1.54  %Background operators:
% 3.27/1.54  
% 3.27/1.54  
% 3.27/1.54  %Foreground operators:
% 3.27/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.27/1.54  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.27/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.27/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.27/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.54  
% 3.27/1.56  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.27/1.56  tff(f_108, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.27/1.56  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.27/1.56  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.27/1.56  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.27/1.56  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.27/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.27/1.56  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.27/1.56  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.27/1.56  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.27/1.56  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.27/1.56  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.27/1.56  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.27/1.56  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.27/1.56  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.27/1.56  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.27/1.56  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.27/1.56  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.27/1.56  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.27/1.56  tff(c_92, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.27/1.56  tff(c_95, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_92])).
% 3.27/1.56  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_95])).
% 3.27/1.56  tff(c_654, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.56  tff(c_658, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_654])).
% 3.27/1.56  tff(c_693, plain, (![B_123, A_124]: (k7_relat_1(B_123, A_124)=B_123 | ~v4_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.56  tff(c_696, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_658, c_693])).
% 3.27/1.56  tff(c_699, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_696])).
% 3.27/1.56  tff(c_709, plain, (![B_127, A_128]: (k2_relat_1(k7_relat_1(B_127, A_128))=k9_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.27/1.56  tff(c_727, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_699, c_709])).
% 3.27/1.56  tff(c_731, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_727])).
% 3.27/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.56  tff(c_659, plain, (![B_119, A_120]: (v5_relat_1(B_119, A_120) | ~r1_tarski(k2_relat_1(B_119), A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.27/1.56  tff(c_673, plain, (![B_119]: (v5_relat_1(B_119, k2_relat_1(B_119)) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_6, c_659])).
% 3.27/1.56  tff(c_1228, plain, (![B_168, A_169]: (v5_relat_1(k7_relat_1(B_168, A_169), k9_relat_1(B_168, A_169)) | ~v1_relat_1(k7_relat_1(B_168, A_169)) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_709, c_673])).
% 3.27/1.56  tff(c_1240, plain, (v5_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_699, c_1228])).
% 3.27/1.56  tff(c_1253, plain, (v5_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_98, c_699, c_731, c_1240])).
% 3.27/1.56  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.27/1.56  tff(c_741, plain, (![B_132, A_133]: (k5_relat_1(B_132, k6_relat_1(A_133))=B_132 | ~r1_tarski(k2_relat_1(B_132), A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.27/1.56  tff(c_755, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_741])).
% 3.27/1.56  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.27/1.56  tff(c_26, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.27/1.56  tff(c_776, plain, (![A_135, B_136]: (k10_relat_1(A_135, k1_relat_1(B_136))=k1_relat_1(k5_relat_1(A_135, B_136)) | ~v1_relat_1(B_136) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.56  tff(c_785, plain, (![A_135, A_19]: (k1_relat_1(k5_relat_1(A_135, k6_relat_1(A_19)))=k10_relat_1(A_135, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_26, c_776])).
% 3.27/1.56  tff(c_889, plain, (![A_145, A_146]: (k1_relat_1(k5_relat_1(A_145, k6_relat_1(A_146)))=k10_relat_1(A_145, A_146) | ~v1_relat_1(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_785])).
% 3.27/1.56  tff(c_907, plain, (![B_7, A_6]: (k10_relat_1(B_7, A_6)=k1_relat_1(B_7) | ~v1_relat_1(B_7) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_755, c_889])).
% 3.27/1.56  tff(c_1258, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1253, c_907])).
% 3.27/1.56  tff(c_1261, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1258])).
% 3.27/1.56  tff(c_1263, plain, (![A_170, B_171, C_172, D_173]: (k8_relset_1(A_170, B_171, C_172, D_173)=k10_relat_1(C_172, D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.27/1.56  tff(c_1266, plain, (![D_173]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_173)=k10_relat_1('#skF_3', D_173))), inference(resolution, [status(thm)], [c_46, c_1263])).
% 3.27/1.56  tff(c_1137, plain, (![A_161, B_162, C_163, D_164]: (k7_relset_1(A_161, B_162, C_163, D_164)=k9_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.27/1.56  tff(c_1140, plain, (![D_164]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_164)=k9_relat_1('#skF_3', D_164))), inference(resolution, [status(thm)], [c_46, c_1137])).
% 3.27/1.56  tff(c_879, plain, (![A_142, B_143, C_144]: (k1_relset_1(A_142, B_143, C_144)=k1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.27/1.56  tff(c_883, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_879])).
% 3.27/1.56  tff(c_18, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.27/1.56  tff(c_134, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.27/1.56  tff(c_138, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_134])).
% 3.27/1.56  tff(c_193, plain, (![B_68, A_69]: (k5_relat_1(B_68, k6_relat_1(A_69))=B_68 | ~r1_tarski(k2_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.27/1.56  tff(c_207, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_193])).
% 3.27/1.56  tff(c_239, plain, (![A_74, B_75]: (k10_relat_1(A_74, k1_relat_1(B_75))=k1_relat_1(k5_relat_1(A_74, B_75)) | ~v1_relat_1(B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.56  tff(c_248, plain, (![A_74, A_19]: (k1_relat_1(k5_relat_1(A_74, k6_relat_1(A_19)))=k10_relat_1(A_74, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_26, c_239])).
% 3.27/1.56  tff(c_342, plain, (![A_81, A_82]: (k1_relat_1(k5_relat_1(A_81, k6_relat_1(A_82)))=k10_relat_1(A_81, A_82) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_248])).
% 3.27/1.56  tff(c_596, plain, (![B_108, A_109]: (k10_relat_1(B_108, A_109)=k1_relat_1(B_108) | ~v1_relat_1(B_108) | ~v5_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(superposition, [status(thm), theory('equality')], [c_207, c_342])).
% 3.27/1.56  tff(c_608, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_596])).
% 3.27/1.56  tff(c_618, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_608])).
% 3.27/1.56  tff(c_582, plain, (![A_103, B_104, C_105, D_106]: (k8_relset_1(A_103, B_104, C_105, D_106)=k10_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.27/1.56  tff(c_585, plain, (![D_106]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_106)=k10_relat_1('#skF_3', D_106))), inference(resolution, [status(thm)], [c_46, c_582])).
% 3.27/1.56  tff(c_549, plain, (![A_96, B_97, C_98, D_99]: (k7_relset_1(A_96, B_97, C_98, D_99)=k9_relat_1(C_98, D_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.27/1.56  tff(c_552, plain, (![D_99]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_99)=k9_relat_1('#skF_3', D_99))), inference(resolution, [status(thm)], [c_46, c_549])).
% 3.27/1.56  tff(c_466, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.27/1.56  tff(c_470, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_466])).
% 3.27/1.56  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.27/1.56  tff(c_99, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.27/1.56  tff(c_471, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_99])).
% 3.27/1.56  tff(c_553, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_552, c_471])).
% 3.27/1.56  tff(c_586, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_553])).
% 3.27/1.56  tff(c_619, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_586])).
% 3.27/1.56  tff(c_626, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_619])).
% 3.27/1.56  tff(c_630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_626])).
% 3.27/1.56  tff(c_631, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.27/1.56  tff(c_884, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_631])).
% 3.27/1.56  tff(c_1141, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_884])).
% 3.27/1.56  tff(c_1142, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_1141])).
% 3.27/1.56  tff(c_1284, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1142])).
% 3.27/1.56  tff(c_1289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1261, c_1284])).
% 3.27/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.56  
% 3.27/1.56  Inference rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Ref     : 0
% 3.27/1.56  #Sup     : 263
% 3.27/1.56  #Fact    : 0
% 3.27/1.56  #Define  : 0
% 3.27/1.56  #Split   : 1
% 3.27/1.56  #Chain   : 0
% 3.27/1.56  #Close   : 0
% 3.27/1.56  
% 3.27/1.56  Ordering : KBO
% 3.27/1.56  
% 3.27/1.56  Simplification rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Subsume      : 11
% 3.27/1.56  #Demod        : 238
% 3.27/1.56  #Tautology    : 157
% 3.27/1.56  #SimpNegUnit  : 0
% 3.27/1.56  #BackRed      : 10
% 3.27/1.56  
% 3.27/1.56  #Partial instantiations: 0
% 3.27/1.56  #Strategies tried      : 1
% 3.27/1.56  
% 3.27/1.56  Timing (in seconds)
% 3.27/1.56  ----------------------
% 3.27/1.56  Preprocessing        : 0.35
% 3.27/1.56  Parsing              : 0.19
% 3.27/1.56  CNF conversion       : 0.02
% 3.27/1.56  Main loop            : 0.40
% 3.27/1.56  Inferencing          : 0.16
% 3.27/1.56  Reduction            : 0.13
% 3.27/1.56  Demodulation         : 0.10
% 3.27/1.56  BG Simplification    : 0.02
% 3.27/1.56  Subsumption          : 0.06
% 3.27/1.56  Abstraction          : 0.02
% 3.27/1.56  MUC search           : 0.00
% 3.27/1.56  Cooper               : 0.00
% 3.27/1.56  Total                : 0.79
% 3.27/1.56  Index Insertion      : 0.00
% 3.27/1.56  Index Deletion       : 0.00
% 3.27/1.56  Index Matching       : 0.00
% 3.27/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
