%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:00 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 268 expanded)
%              Number of leaves         :   40 ( 105 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 ( 483 expanded)
%              Number of equality atoms :   67 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_849,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k8_relset_1(A_160,B_161,C_162,D_163) = k10_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_852,plain,(
    ! [D_163] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_163) = k10_relat_1('#skF_3',D_163) ),
    inference(resolution,[status(thm)],[c_44,c_849])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_65])).

tff(c_597,plain,(
    ! [C_126,A_127,B_128] :
      ( v4_relat_1(C_126,A_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_601,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_597])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_604,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_601,c_24])).

tff(c_607,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_604])).

tff(c_617,plain,(
    ! [B_132,A_133] :
      ( k2_relat_1(k7_relat_1(B_132,A_133)) = k9_relat_1(B_132,A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_635,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_617])).

tff(c_639,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_635])).

tff(c_812,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k7_relset_1(A_155,B_156,C_157,D_158) = k9_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_815,plain,(
    ! [D_158] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_158) = k9_relat_1('#skF_3',D_158) ),
    inference(resolution,[status(thm)],[c_44,c_812])).

tff(c_719,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_723,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_719])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_340,plain,(
    ! [D_101,B_102,C_103,A_104] :
      ( m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(B_102,C_103)))
      | ~ r1_tarski(k1_relat_1(D_101),B_102)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_104,C_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_344,plain,(
    ! [B_105] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_105,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_105) ) ),
    inference(resolution,[status(thm)],[c_44,c_340])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v4_relat_1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_377,plain,(
    ! [B_106] :
      ( v4_relat_1('#skF_3',B_106)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_106) ) ),
    inference(resolution,[status(thm)],[c_344,c_30])).

tff(c_387,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_377])).

tff(c_390,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_387,c_24])).

tff(c_393,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_390])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_411,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_18])).

tff(c_417,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_411])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,k10_relat_1(B_21,k9_relat_1(B_21,A_20)))
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,A_14),k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [B_86,A_87] :
      ( k10_relat_1(B_86,A_87) = k1_relat_1(B_86)
      | ~ r1_tarski(k1_relat_1(B_86),k10_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_266,plain,(
    ! [B_21] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,k1_relat_1(B_21))) = k1_relat_1(B_21)
      | ~ r1_tarski(k1_relat_1(B_21),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_262])).

tff(c_272,plain,(
    ! [B_21] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,k1_relat_1(B_21))) = k1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_266])).

tff(c_427,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_272])).

tff(c_436,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_427])).

tff(c_94,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_98,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_94])).

tff(c_86,plain,(
    ! [B_57,A_58] :
      ( r1_tarski(k2_relat_1(B_57),A_58)
      | ~ v5_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    ! [B_74,A_75] :
      ( k3_xboole_0(k2_relat_1(B_74),A_75) = k2_relat_1(B_74)
      | ~ v5_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k3_xboole_0(k2_relat_1(B_17),A_16)) = k10_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_553,plain,(
    ! [B_117,A_118] :
      ( k10_relat_1(B_117,k2_relat_1(B_117)) = k10_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117)
      | ~ v5_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_22])).

tff(c_561,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_553])).

tff(c_570,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_436,c_561])).

tff(c_314,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_relset_1(A_94,B_95,C_96,D_97) = k9_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_317,plain,(
    ! [D_97] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_97) = k9_relat_1('#skF_3',D_97) ),
    inference(resolution,[status(thm)],[c_44,c_314])).

tff(c_273,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k8_relset_1(A_88,B_89,C_90,D_91) = k10_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_276,plain,(
    ! [D_91] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_91) = k10_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_44,c_273])).

tff(c_218,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_222,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_218])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_84,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_223,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_84])).

tff(c_277,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_223])).

tff(c_318,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_277])).

tff(c_571,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_318])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_571])).

tff(c_575,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_742,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_575])).

tff(c_817,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_742])).

tff(c_818,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_817])).

tff(c_854,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_818])).

tff(c_879,plain,(
    ! [D_165,B_166,C_167,A_168] :
      ( m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(B_166,C_167)))
      | ~ r1_tarski(k1_relat_1(D_165),B_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_168,C_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_895,plain,(
    ! [B_169] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_169,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_169) ) ),
    inference(resolution,[status(thm)],[c_44,c_879])).

tff(c_928,plain,(
    ! [B_170] :
      ( v4_relat_1('#skF_3',B_170)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_170) ) ),
    inference(resolution,[status(thm)],[c_895,c_30])).

tff(c_938,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_928])).

tff(c_952,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_938,c_24])).

tff(c_955,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_952])).

tff(c_962,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_18])).

tff(c_968,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_962])).

tff(c_763,plain,(
    ! [B_150,A_151] :
      ( k10_relat_1(B_150,A_151) = k1_relat_1(B_150)
      | ~ r1_tarski(k1_relat_1(B_150),k10_relat_1(B_150,A_151))
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_767,plain,(
    ! [B_21] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,k1_relat_1(B_21))) = k1_relat_1(B_21)
      | ~ r1_tarski(k1_relat_1(B_21),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_763])).

tff(c_773,plain,(
    ! [B_21] :
      ( k10_relat_1(B_21,k9_relat_1(B_21,k1_relat_1(B_21))) = k1_relat_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_767])).

tff(c_978,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_773])).

tff(c_987,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_978])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.47  
% 3.03/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.47  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.03/1.47  
% 3.03/1.47  %Foreground sorts:
% 3.03/1.47  
% 3.03/1.47  
% 3.03/1.47  %Background operators:
% 3.03/1.47  
% 3.03/1.47  
% 3.03/1.47  %Foreground operators:
% 3.03/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.03/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.03/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.03/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.03/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.03/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.03/1.47  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.03/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.47  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.47  
% 3.16/1.49  tff(f_109, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.16/1.49  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.16/1.49  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.49  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.49  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.16/1.49  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.16/1.49  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.16/1.49  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.16/1.49  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.49  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.16/1.49  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.16/1.49  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.16/1.49  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.16/1.49  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.16/1.49  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.16/1.49  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.49  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.49  tff(c_849, plain, (![A_160, B_161, C_162, D_163]: (k8_relset_1(A_160, B_161, C_162, D_163)=k10_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.49  tff(c_852, plain, (![D_163]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_163)=k10_relat_1('#skF_3', D_163))), inference(resolution, [status(thm)], [c_44, c_849])).
% 3.16/1.49  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.49  tff(c_62, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.49  tff(c_65, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_62])).
% 3.16/1.49  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_65])).
% 3.16/1.49  tff(c_597, plain, (![C_126, A_127, B_128]: (v4_relat_1(C_126, A_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.16/1.49  tff(c_601, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_597])).
% 3.16/1.49  tff(c_24, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.49  tff(c_604, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_601, c_24])).
% 3.16/1.49  tff(c_607, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_604])).
% 3.16/1.49  tff(c_617, plain, (![B_132, A_133]: (k2_relat_1(k7_relat_1(B_132, A_133))=k9_relat_1(B_132, A_133) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.49  tff(c_635, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_607, c_617])).
% 3.16/1.49  tff(c_639, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_635])).
% 3.16/1.49  tff(c_812, plain, (![A_155, B_156, C_157, D_158]: (k7_relset_1(A_155, B_156, C_157, D_158)=k9_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.49  tff(c_815, plain, (![D_158]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_158)=k9_relat_1('#skF_3', D_158))), inference(resolution, [status(thm)], [c_44, c_812])).
% 3.16/1.49  tff(c_719, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.49  tff(c_723, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_719])).
% 3.16/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.49  tff(c_340, plain, (![D_101, B_102, C_103, A_104]: (m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(B_102, C_103))) | ~r1_tarski(k1_relat_1(D_101), B_102) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_104, C_103))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.49  tff(c_344, plain, (![B_105]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_105, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_105))), inference(resolution, [status(thm)], [c_44, c_340])).
% 3.16/1.49  tff(c_30, plain, (![C_24, A_22, B_23]: (v4_relat_1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.16/1.49  tff(c_377, plain, (![B_106]: (v4_relat_1('#skF_3', B_106) | ~r1_tarski(k1_relat_1('#skF_3'), B_106))), inference(resolution, [status(thm)], [c_344, c_30])).
% 3.16/1.49  tff(c_387, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_377])).
% 3.16/1.49  tff(c_390, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_387, c_24])).
% 3.16/1.49  tff(c_393, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_390])).
% 3.16/1.49  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.49  tff(c_411, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_18])).
% 3.16/1.49  tff(c_417, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_411])).
% 3.16/1.49  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, k10_relat_1(B_21, k9_relat_1(B_21, A_20))) | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.49  tff(c_20, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, A_14), k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.49  tff(c_74, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.49  tff(c_262, plain, (![B_86, A_87]: (k10_relat_1(B_86, A_87)=k1_relat_1(B_86) | ~r1_tarski(k1_relat_1(B_86), k10_relat_1(B_86, A_87)) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.16/1.49  tff(c_266, plain, (![B_21]: (k10_relat_1(B_21, k9_relat_1(B_21, k1_relat_1(B_21)))=k1_relat_1(B_21) | ~r1_tarski(k1_relat_1(B_21), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_26, c_262])).
% 3.16/1.49  tff(c_272, plain, (![B_21]: (k10_relat_1(B_21, k9_relat_1(B_21, k1_relat_1(B_21)))=k1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_266])).
% 3.16/1.49  tff(c_427, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_417, c_272])).
% 3.16/1.49  tff(c_436, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_427])).
% 3.16/1.49  tff(c_94, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.16/1.49  tff(c_98, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_94])).
% 3.16/1.49  tff(c_86, plain, (![B_57, A_58]: (r1_tarski(k2_relat_1(B_57), A_58) | ~v5_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.49  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.49  tff(c_184, plain, (![B_74, A_75]: (k3_xboole_0(k2_relat_1(B_74), A_75)=k2_relat_1(B_74) | ~v5_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_86, c_8])).
% 3.16/1.49  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k3_xboole_0(k2_relat_1(B_17), A_16))=k10_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.49  tff(c_553, plain, (![B_117, A_118]: (k10_relat_1(B_117, k2_relat_1(B_117))=k10_relat_1(B_117, A_118) | ~v1_relat_1(B_117) | ~v5_relat_1(B_117, A_118) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_184, c_22])).
% 3.16/1.49  tff(c_561, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_553])).
% 3.16/1.49  tff(c_570, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_436, c_561])).
% 3.16/1.49  tff(c_314, plain, (![A_94, B_95, C_96, D_97]: (k7_relset_1(A_94, B_95, C_96, D_97)=k9_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.49  tff(c_317, plain, (![D_97]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_97)=k9_relat_1('#skF_3', D_97))), inference(resolution, [status(thm)], [c_44, c_314])).
% 3.16/1.49  tff(c_273, plain, (![A_88, B_89, C_90, D_91]: (k8_relset_1(A_88, B_89, C_90, D_91)=k10_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.49  tff(c_276, plain, (![D_91]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_91)=k10_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_44, c_273])).
% 3.16/1.49  tff(c_218, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.49  tff(c_222, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_218])).
% 3.16/1.49  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.49  tff(c_84, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.16/1.49  tff(c_223, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_84])).
% 3.16/1.49  tff(c_277, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_223])).
% 3.16/1.49  tff(c_318, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_277])).
% 3.16/1.49  tff(c_571, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_318])).
% 3.16/1.49  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_417, c_571])).
% 3.16/1.49  tff(c_575, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.16/1.49  tff(c_742, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_723, c_575])).
% 3.16/1.49  tff(c_817, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_742])).
% 3.16/1.49  tff(c_818, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_817])).
% 3.16/1.49  tff(c_854, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_852, c_818])).
% 3.16/1.49  tff(c_879, plain, (![D_165, B_166, C_167, A_168]: (m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(B_166, C_167))) | ~r1_tarski(k1_relat_1(D_165), B_166) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_168, C_167))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.49  tff(c_895, plain, (![B_169]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_169, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_169))), inference(resolution, [status(thm)], [c_44, c_879])).
% 3.16/1.49  tff(c_928, plain, (![B_170]: (v4_relat_1('#skF_3', B_170) | ~r1_tarski(k1_relat_1('#skF_3'), B_170))), inference(resolution, [status(thm)], [c_895, c_30])).
% 3.16/1.49  tff(c_938, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_928])).
% 3.16/1.49  tff(c_952, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_938, c_24])).
% 3.16/1.49  tff(c_955, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_952])).
% 3.16/1.49  tff(c_962, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_955, c_18])).
% 3.16/1.49  tff(c_968, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_962])).
% 3.16/1.49  tff(c_763, plain, (![B_150, A_151]: (k10_relat_1(B_150, A_151)=k1_relat_1(B_150) | ~r1_tarski(k1_relat_1(B_150), k10_relat_1(B_150, A_151)) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_20, c_74])).
% 3.16/1.49  tff(c_767, plain, (![B_21]: (k10_relat_1(B_21, k9_relat_1(B_21, k1_relat_1(B_21)))=k1_relat_1(B_21) | ~r1_tarski(k1_relat_1(B_21), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_26, c_763])).
% 3.16/1.49  tff(c_773, plain, (![B_21]: (k10_relat_1(B_21, k9_relat_1(B_21, k1_relat_1(B_21)))=k1_relat_1(B_21) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_767])).
% 3.16/1.49  tff(c_978, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_968, c_773])).
% 3.16/1.49  tff(c_987, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_978])).
% 3.16/1.49  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_854, c_987])).
% 3.16/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  Inference rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Ref     : 0
% 3.16/1.49  #Sup     : 222
% 3.16/1.49  #Fact    : 0
% 3.16/1.49  #Define  : 0
% 3.16/1.49  #Split   : 3
% 3.16/1.49  #Chain   : 0
% 3.16/1.49  #Close   : 0
% 3.16/1.49  
% 3.16/1.49  Ordering : KBO
% 3.16/1.49  
% 3.16/1.49  Simplification rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Subsume      : 9
% 3.16/1.49  #Demod        : 115
% 3.16/1.49  #Tautology    : 114
% 3.16/1.49  #SimpNegUnit  : 1
% 3.16/1.49  #BackRed      : 12
% 3.16/1.49  
% 3.16/1.49  #Partial instantiations: 0
% 3.16/1.49  #Strategies tried      : 1
% 3.16/1.49  
% 3.16/1.49  Timing (in seconds)
% 3.16/1.49  ----------------------
% 3.16/1.49  Preprocessing        : 0.33
% 3.16/1.49  Parsing              : 0.18
% 3.16/1.49  CNF conversion       : 0.02
% 3.16/1.49  Main loop            : 0.38
% 3.16/1.49  Inferencing          : 0.14
% 3.16/1.50  Reduction            : 0.12
% 3.16/1.50  Demodulation         : 0.08
% 3.16/1.50  BG Simplification    : 0.02
% 3.16/1.50  Subsumption          : 0.06
% 3.16/1.50  Abstraction          : 0.02
% 3.16/1.50  MUC search           : 0.00
% 3.16/1.50  Cooper               : 0.00
% 3.16/1.50  Total                : 0.75
% 3.16/1.50  Index Insertion      : 0.00
% 3.16/1.50  Index Deletion       : 0.00
% 3.16/1.50  Index Matching       : 0.00
% 3.16/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
