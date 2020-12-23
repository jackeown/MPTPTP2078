%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:57 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 174 expanded)
%              Number of leaves         :   42 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  162 ( 291 expanded)
%              Number of equality atoms :   69 ( 112 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_86,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_86])).

tff(c_467,plain,(
    ! [C_120,A_121,B_122] :
      ( v4_relat_1(C_120,A_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_471,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_467])).

tff(c_472,plain,(
    ! [B_123,A_124] :
      ( k7_relat_1(B_123,A_124) = B_123
      | ~ v4_relat_1(B_123,A_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_475,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_471,c_472])).

tff(c_478,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_475])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_482,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_12])).

tff(c_486,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_482])).

tff(c_779,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k7_relset_1(A_162,B_163,C_164,D_165) = k9_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_782,plain,(
    ! [D_165] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_165) = k9_relat_1('#skF_3',D_165) ),
    inference(resolution,[status(thm)],[c_42,c_779])).

tff(c_717,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k8_relset_1(A_155,B_156,C_157,D_158) = k10_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_720,plain,(
    ! [D_158] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_158) = k10_relat_1('#skF_3',D_158) ),
    inference(resolution,[status(thm)],[c_42,c_717])).

tff(c_594,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_598,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_594])).

tff(c_10,plain,(
    ! [A_6] :
      ( k9_relat_1(A_6,k1_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_115,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [B_67,A_68] :
      ( k5_relat_1(B_67,k6_relat_1(A_68)) = B_67
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_173,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_271,plain,(
    ! [A_84,B_85] :
      ( k10_relat_1(A_84,k1_relat_1(B_85)) = k1_relat_1(k5_relat_1(A_84,B_85))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_280,plain,(
    ! [A_84,A_16] :
      ( k1_relat_1(k5_relat_1(A_84,k6_relat_1(A_16))) = k10_relat_1(A_84,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_271])).

tff(c_285,plain,(
    ! [A_86,A_87] :
      ( k1_relat_1(k5_relat_1(A_86,k6_relat_1(A_87))) = k10_relat_1(A_86,A_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_280])).

tff(c_394,plain,(
    ! [B_105,A_106] :
      ( k10_relat_1(B_105,A_106) = k1_relat_1(B_105)
      | ~ v1_relat_1(B_105)
      | ~ v5_relat_1(B_105,A_106)
      | ~ v1_relat_1(B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_285])).

tff(c_397,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_394])).

tff(c_403,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_397])).

tff(c_380,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_383,plain,(
    ! [D_103] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_103) = k9_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_42,c_380])).

tff(c_366,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_369,plain,(
    ! [D_98] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_98) = k10_relat_1('#skF_3',D_98) ),
    inference(resolution,[status(thm)],[c_42,c_366])).

tff(c_261,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(A_81,B_82,C_83) = k2_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_265,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_261])).

tff(c_40,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_91,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_266,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_91])).

tff(c_370,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_266])).

tff(c_384,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_370])).

tff(c_407,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_384])).

tff(c_414,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_407])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_414])).

tff(c_419,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_699,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_419])).

tff(c_726,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_699])).

tff(c_783,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_726])).

tff(c_784,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_783])).

tff(c_440,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_444,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_440])).

tff(c_492,plain,(
    ! [B_125,A_126] :
      ( k5_relat_1(B_125,k6_relat_1(A_126)) = B_125
      | ~ r1_tarski(k2_relat_1(B_125),A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_502,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_492])).

tff(c_603,plain,(
    ! [A_142,B_143] :
      ( k10_relat_1(A_142,k1_relat_1(B_143)) = k1_relat_1(k5_relat_1(A_142,B_143))
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_612,plain,(
    ! [A_142,A_16] :
      ( k1_relat_1(k5_relat_1(A_142,k6_relat_1(A_16))) = k10_relat_1(A_142,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_603])).

tff(c_617,plain,(
    ! [A_144,A_145] :
      ( k1_relat_1(k5_relat_1(A_144,k6_relat_1(A_145))) = k10_relat_1(A_144,A_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_612])).

tff(c_704,plain,(
    ! [B_153,A_154] :
      ( k10_relat_1(B_153,A_154) = k1_relat_1(B_153)
      | ~ v1_relat_1(B_153)
      | ~ v5_relat_1(B_153,A_154)
      | ~ v1_relat_1(B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_617])).

tff(c_707,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_444,c_704])).

tff(c_713,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_707])).

tff(c_445,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(k2_relat_1(B_116),A_117)
      | ~ v5_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_562,plain,(
    ! [B_135,A_136] :
      ( k3_xboole_0(k2_relat_1(B_135),A_136) = k2_relat_1(B_135)
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_445,c_2])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k10_relat_1(B_10,k3_xboole_0(k2_relat_1(B_10),A_9)) = k10_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_835,plain,(
    ! [B_171,A_172] :
      ( k10_relat_1(B_171,k2_relat_1(B_171)) = k10_relat_1(B_171,A_172)
      | ~ v1_relat_1(B_171)
      | ~ v5_relat_1(B_171,A_172)
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_14])).

tff(c_839,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_444,c_835])).

tff(c_845,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_713,c_839])).

tff(c_847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_784,c_845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.60  
% 3.12/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.60  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.12/1.60  
% 3.12/1.60  %Foreground sorts:
% 3.12/1.60  
% 3.12/1.60  
% 3.12/1.60  %Background operators:
% 3.12/1.60  
% 3.12/1.60  
% 3.12/1.60  %Foreground operators:
% 3.12/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.12/1.60  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.12/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.12/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.60  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.12/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.12/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.12/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.12/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.60  
% 3.35/1.63  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.35/1.63  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.35/1.63  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.35/1.63  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.35/1.63  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.35/1.63  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.35/1.63  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.35/1.63  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.35/1.63  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.35/1.63  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.35/1.63  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.35/1.63  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.35/1.63  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.35/1.63  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.35/1.63  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.35/1.63  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.35/1.63  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.35/1.63  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.35/1.63  tff(c_86, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.35/1.63  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_86])).
% 3.35/1.63  tff(c_467, plain, (![C_120, A_121, B_122]: (v4_relat_1(C_120, A_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.35/1.63  tff(c_471, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_467])).
% 3.35/1.63  tff(c_472, plain, (![B_123, A_124]: (k7_relat_1(B_123, A_124)=B_123 | ~v4_relat_1(B_123, A_124) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.35/1.63  tff(c_475, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_471, c_472])).
% 3.35/1.63  tff(c_478, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_475])).
% 3.35/1.63  tff(c_12, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.63  tff(c_482, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_478, c_12])).
% 3.35/1.63  tff(c_486, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_482])).
% 3.35/1.63  tff(c_779, plain, (![A_162, B_163, C_164, D_165]: (k7_relset_1(A_162, B_163, C_164, D_165)=k9_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.63  tff(c_782, plain, (![D_165]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_165)=k9_relat_1('#skF_3', D_165))), inference(resolution, [status(thm)], [c_42, c_779])).
% 3.35/1.63  tff(c_717, plain, (![A_155, B_156, C_157, D_158]: (k8_relset_1(A_155, B_156, C_157, D_158)=k10_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.35/1.63  tff(c_720, plain, (![D_158]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_158)=k10_relat_1('#skF_3', D_158))), inference(resolution, [status(thm)], [c_42, c_717])).
% 3.35/1.63  tff(c_594, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.35/1.63  tff(c_598, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_594])).
% 3.35/1.63  tff(c_10, plain, (![A_6]: (k9_relat_1(A_6, k1_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.63  tff(c_111, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.35/1.63  tff(c_115, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_111])).
% 3.35/1.63  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.63  tff(c_163, plain, (![B_67, A_68]: (k5_relat_1(B_67, k6_relat_1(A_68))=B_67 | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.35/1.63  tff(c_173, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_163])).
% 3.35/1.63  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.63  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.35/1.63  tff(c_271, plain, (![A_84, B_85]: (k10_relat_1(A_84, k1_relat_1(B_85))=k1_relat_1(k5_relat_1(A_84, B_85)) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.63  tff(c_280, plain, (![A_84, A_16]: (k1_relat_1(k5_relat_1(A_84, k6_relat_1(A_16)))=k10_relat_1(A_84, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_20, c_271])).
% 3.35/1.63  tff(c_285, plain, (![A_86, A_87]: (k1_relat_1(k5_relat_1(A_86, k6_relat_1(A_87)))=k10_relat_1(A_86, A_87) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_280])).
% 3.35/1.63  tff(c_394, plain, (![B_105, A_106]: (k10_relat_1(B_105, A_106)=k1_relat_1(B_105) | ~v1_relat_1(B_105) | ~v5_relat_1(B_105, A_106) | ~v1_relat_1(B_105))), inference(superposition, [status(thm), theory('equality')], [c_173, c_285])).
% 3.35/1.63  tff(c_397, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_394])).
% 3.35/1.63  tff(c_403, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_397])).
% 3.35/1.63  tff(c_380, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.35/1.63  tff(c_383, plain, (![D_103]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_103)=k9_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_42, c_380])).
% 3.35/1.63  tff(c_366, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.35/1.63  tff(c_369, plain, (![D_98]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_98)=k10_relat_1('#skF_3', D_98))), inference(resolution, [status(thm)], [c_42, c_366])).
% 3.35/1.63  tff(c_261, plain, (![A_81, B_82, C_83]: (k2_relset_1(A_81, B_82, C_83)=k2_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.35/1.63  tff(c_265, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_261])).
% 3.35/1.63  tff(c_40, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.35/1.63  tff(c_91, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.35/1.63  tff(c_266, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_91])).
% 3.35/1.63  tff(c_370, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_266])).
% 3.35/1.63  tff(c_384, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_370])).
% 3.35/1.63  tff(c_407, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_384])).
% 3.35/1.63  tff(c_414, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_407])).
% 3.35/1.63  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_414])).
% 3.35/1.63  tff(c_419, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.35/1.63  tff(c_699, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_419])).
% 3.35/1.63  tff(c_726, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_699])).
% 3.35/1.63  tff(c_783, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_726])).
% 3.35/1.63  tff(c_784, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_486, c_783])).
% 3.35/1.63  tff(c_440, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.35/1.63  tff(c_444, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_440])).
% 3.35/1.63  tff(c_492, plain, (![B_125, A_126]: (k5_relat_1(B_125, k6_relat_1(A_126))=B_125 | ~r1_tarski(k2_relat_1(B_125), A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.35/1.63  tff(c_502, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_492])).
% 3.35/1.63  tff(c_603, plain, (![A_142, B_143]: (k10_relat_1(A_142, k1_relat_1(B_143))=k1_relat_1(k5_relat_1(A_142, B_143)) | ~v1_relat_1(B_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.63  tff(c_612, plain, (![A_142, A_16]: (k1_relat_1(k5_relat_1(A_142, k6_relat_1(A_16)))=k10_relat_1(A_142, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_20, c_603])).
% 3.35/1.63  tff(c_617, plain, (![A_144, A_145]: (k1_relat_1(k5_relat_1(A_144, k6_relat_1(A_145)))=k10_relat_1(A_144, A_145) | ~v1_relat_1(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_612])).
% 3.35/1.63  tff(c_704, plain, (![B_153, A_154]: (k10_relat_1(B_153, A_154)=k1_relat_1(B_153) | ~v1_relat_1(B_153) | ~v5_relat_1(B_153, A_154) | ~v1_relat_1(B_153))), inference(superposition, [status(thm), theory('equality')], [c_502, c_617])).
% 3.35/1.63  tff(c_707, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_444, c_704])).
% 3.35/1.63  tff(c_713, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_707])).
% 3.35/1.63  tff(c_445, plain, (![B_116, A_117]: (r1_tarski(k2_relat_1(B_116), A_117) | ~v5_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.35/1.63  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.63  tff(c_562, plain, (![B_135, A_136]: (k3_xboole_0(k2_relat_1(B_135), A_136)=k2_relat_1(B_135) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_445, c_2])).
% 3.35/1.63  tff(c_14, plain, (![B_10, A_9]: (k10_relat_1(B_10, k3_xboole_0(k2_relat_1(B_10), A_9))=k10_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.63  tff(c_835, plain, (![B_171, A_172]: (k10_relat_1(B_171, k2_relat_1(B_171))=k10_relat_1(B_171, A_172) | ~v1_relat_1(B_171) | ~v5_relat_1(B_171, A_172) | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_562, c_14])).
% 3.35/1.63  tff(c_839, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_444, c_835])).
% 3.35/1.63  tff(c_845, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_713, c_839])).
% 3.35/1.63  tff(c_847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_784, c_845])).
% 3.35/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.63  
% 3.35/1.63  Inference rules
% 3.35/1.63  ----------------------
% 3.35/1.63  #Ref     : 0
% 3.35/1.63  #Sup     : 185
% 3.35/1.63  #Fact    : 0
% 3.35/1.63  #Define  : 0
% 3.35/1.63  #Split   : 1
% 3.35/1.63  #Chain   : 0
% 3.35/1.63  #Close   : 0
% 3.35/1.63  
% 3.35/1.63  Ordering : KBO
% 3.35/1.63  
% 3.35/1.63  Simplification rules
% 3.35/1.63  ----------------------
% 3.35/1.63  #Subsume      : 13
% 3.35/1.63  #Demod        : 81
% 3.35/1.63  #Tautology    : 96
% 3.35/1.63  #SimpNegUnit  : 1
% 3.35/1.63  #BackRed      : 8
% 3.35/1.63  
% 3.35/1.63  #Partial instantiations: 0
% 3.35/1.63  #Strategies tried      : 1
% 3.35/1.63  
% 3.35/1.63  Timing (in seconds)
% 3.35/1.63  ----------------------
% 3.35/1.63  Preprocessing        : 0.34
% 3.35/1.63  Parsing              : 0.18
% 3.35/1.63  CNF conversion       : 0.02
% 3.35/1.63  Main loop            : 0.51
% 3.35/1.63  Inferencing          : 0.22
% 3.35/1.63  Reduction            : 0.15
% 3.35/1.63  Demodulation         : 0.11
% 3.35/1.63  BG Simplification    : 0.03
% 3.35/1.63  Subsumption          : 0.06
% 3.35/1.63  Abstraction          : 0.03
% 3.35/1.63  MUC search           : 0.00
% 3.35/1.63  Cooper               : 0.00
% 3.35/1.63  Total                : 0.89
% 3.35/1.63  Index Insertion      : 0.00
% 3.35/1.63  Index Deletion       : 0.00
% 3.35/1.63  Index Matching       : 0.00
% 3.35/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
