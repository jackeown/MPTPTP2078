%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 131 expanded)
%              Number of leaves         :   42 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 187 expanded)
%              Number of equality atoms :   58 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_118,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_118])).

tff(c_909,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_913,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_909])).

tff(c_975,plain,(
    ! [A_135,B_136,C_137] :
      ( m1_subset_1(k2_relset_1(A_135,B_136,C_137),k1_zfmisc_1(B_136))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1001,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_975])).

tff(c_1009,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1001])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [B_18,A_17] : k5_relat_1(k6_relat_1(B_18),k6_relat_1(A_17)) = k6_relat_1(k3_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_801,plain,(
    ! [B_122,A_123] :
      ( k9_relat_1(B_122,k2_relat_1(A_123)) = k2_relat_1(k5_relat_1(A_123,B_122))
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_813,plain,(
    ! [A_14,B_122] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_14),B_122)) = k9_relat_1(B_122,A_14)
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_801])).

tff(c_818,plain,(
    ! [A_124,B_125] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_124),B_125)) = k9_relat_1(B_125,A_124)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_813])).

tff(c_839,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_17,B_18))) = k9_relat_1(k6_relat_1(A_17),B_18)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_818])).

tff(c_843,plain,(
    ! [A_17,B_18] : k9_relat_1(k6_relat_1(A_17),B_18) = k3_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_839])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k9_relat_1(k6_relat_1(A_15),B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_844,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_20])).

tff(c_1013,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1009,c_844])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_664,plain,(
    ! [B_111,A_112] :
      ( k10_relat_1(B_111,k3_xboole_0(k2_relat_1(B_111),A_112)) = k10_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_677,plain,(
    ! [B_111,B_2] :
      ( k10_relat_1(B_111,k3_xboole_0(B_2,k2_relat_1(B_111))) = k10_relat_1(B_111,B_2)
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_664])).

tff(c_1017,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_677])).

tff(c_1027,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1017])).

tff(c_12,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1034,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_12])).

tff(c_1041,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1034])).

tff(c_1079,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k8_relset_1(A_142,B_143,C_144,D_145) = k10_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1086,plain,(
    ! [D_145] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_145) = k10_relat_1('#skF_3',D_145) ),
    inference(resolution,[status(thm)],[c_42,c_1079])).

tff(c_791,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_795,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_791])).

tff(c_124,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_128,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_124])).

tff(c_146,plain,(
    ! [B_60,A_61] :
      ( k7_relat_1(B_60,A_61) = B_60
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_149,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_146])).

tff(c_152,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_149])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_156,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_6])).

tff(c_160,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_156])).

tff(c_586,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_593,plain,(
    ! [D_96] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_96) = k9_relat_1('#skF_3',D_96) ),
    inference(resolution,[status(thm)],[c_42,c_586])).

tff(c_263,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_267,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_263])).

tff(c_40,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_123,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_268,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_123])).

tff(c_594,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_268])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_594])).

tff(c_598,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_796,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_598])).

tff(c_1104,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_796])).

tff(c_1107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_1104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  %$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.44  
% 2.78/1.44  %Foreground sorts:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Background operators:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Foreground operators:
% 2.78/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.78/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.78/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.44  
% 2.78/1.45  tff(f_101, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.78/1.45  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.45  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.78/1.45  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.78/1.45  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.78/1.45  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.78/1.45  tff(f_64, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.78/1.45  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.78/1.45  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.78/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.78/1.45  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.78/1.45  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.78/1.45  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.78/1.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.78/1.45  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.78/1.45  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.78/1.45  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.78/1.45  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.78/1.45  tff(c_118, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.78/1.45  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_118])).
% 2.78/1.45  tff(c_909, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.78/1.45  tff(c_913, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_909])).
% 2.78/1.45  tff(c_975, plain, (![A_135, B_136, C_137]: (m1_subset_1(k2_relset_1(A_135, B_136, C_137), k1_zfmisc_1(B_136)) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.45  tff(c_1001, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_913, c_975])).
% 2.78/1.45  tff(c_1009, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1001])).
% 2.78/1.45  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.45  tff(c_18, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.78/1.45  tff(c_22, plain, (![B_18, A_17]: (k5_relat_1(k6_relat_1(B_18), k6_relat_1(A_17))=k6_relat_1(k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.78/1.45  tff(c_801, plain, (![B_122, A_123]: (k9_relat_1(B_122, k2_relat_1(A_123))=k2_relat_1(k5_relat_1(A_123, B_122)) | ~v1_relat_1(B_122) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.78/1.45  tff(c_813, plain, (![A_14, B_122]: (k2_relat_1(k5_relat_1(k6_relat_1(A_14), B_122))=k9_relat_1(B_122, A_14) | ~v1_relat_1(B_122) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_801])).
% 2.78/1.45  tff(c_818, plain, (![A_124, B_125]: (k2_relat_1(k5_relat_1(k6_relat_1(A_124), B_125))=k9_relat_1(B_125, A_124) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_813])).
% 2.78/1.45  tff(c_839, plain, (![A_17, B_18]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_17, B_18)))=k9_relat_1(k6_relat_1(A_17), B_18) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_818])).
% 2.78/1.45  tff(c_843, plain, (![A_17, B_18]: (k9_relat_1(k6_relat_1(A_17), B_18)=k3_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_839])).
% 2.78/1.45  tff(c_20, plain, (![A_15, B_16]: (k9_relat_1(k6_relat_1(A_15), B_16)=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.78/1.45  tff(c_844, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_20])).
% 2.78/1.45  tff(c_1013, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1009, c_844])).
% 2.78/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.45  tff(c_664, plain, (![B_111, A_112]: (k10_relat_1(B_111, k3_xboole_0(k2_relat_1(B_111), A_112))=k10_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.78/1.45  tff(c_677, plain, (![B_111, B_2]: (k10_relat_1(B_111, k3_xboole_0(B_2, k2_relat_1(B_111)))=k10_relat_1(B_111, B_2) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_2, c_664])).
% 2.78/1.45  tff(c_1017, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1013, c_677])).
% 2.78/1.45  tff(c_1027, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1017])).
% 2.78/1.45  tff(c_12, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.78/1.45  tff(c_1034, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1027, c_12])).
% 2.78/1.45  tff(c_1041, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1034])).
% 2.78/1.45  tff(c_1079, plain, (![A_142, B_143, C_144, D_145]: (k8_relset_1(A_142, B_143, C_144, D_145)=k10_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.45  tff(c_1086, plain, (![D_145]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_145)=k10_relat_1('#skF_3', D_145))), inference(resolution, [status(thm)], [c_42, c_1079])).
% 2.78/1.45  tff(c_791, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.45  tff(c_795, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_791])).
% 2.78/1.45  tff(c_124, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.78/1.45  tff(c_128, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_124])).
% 2.78/1.45  tff(c_146, plain, (![B_60, A_61]: (k7_relat_1(B_60, A_61)=B_60 | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.45  tff(c_149, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_146])).
% 2.78/1.45  tff(c_152, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_149])).
% 2.78/1.45  tff(c_6, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.45  tff(c_156, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_6])).
% 2.78/1.45  tff(c_160, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_156])).
% 2.78/1.45  tff(c_586, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.78/1.45  tff(c_593, plain, (![D_96]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_96)=k9_relat_1('#skF_3', D_96))), inference(resolution, [status(thm)], [c_42, c_586])).
% 2.78/1.45  tff(c_263, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.78/1.45  tff(c_267, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_263])).
% 2.78/1.45  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.78/1.45  tff(c_123, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.78/1.45  tff(c_268, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_123])).
% 2.78/1.45  tff(c_594, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_268])).
% 2.78/1.45  tff(c_597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_594])).
% 2.78/1.45  tff(c_598, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.78/1.45  tff(c_796, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_795, c_598])).
% 2.78/1.45  tff(c_1104, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_796])).
% 2.78/1.45  tff(c_1107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1041, c_1104])).
% 2.78/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.45  
% 2.78/1.45  Inference rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Ref     : 0
% 2.78/1.45  #Sup     : 264
% 2.78/1.45  #Fact    : 0
% 2.78/1.45  #Define  : 0
% 2.78/1.45  #Split   : 1
% 2.78/1.45  #Chain   : 0
% 2.78/1.45  #Close   : 0
% 2.78/1.45  
% 2.78/1.45  Ordering : KBO
% 2.78/1.45  
% 2.78/1.45  Simplification rules
% 2.78/1.45  ----------------------
% 2.78/1.45  #Subsume      : 8
% 2.78/1.45  #Demod        : 127
% 2.78/1.45  #Tautology    : 170
% 2.78/1.45  #SimpNegUnit  : 0
% 2.78/1.45  #BackRed      : 9
% 2.78/1.45  
% 2.78/1.45  #Partial instantiations: 0
% 2.78/1.45  #Strategies tried      : 1
% 2.78/1.45  
% 2.78/1.45  Timing (in seconds)
% 2.78/1.45  ----------------------
% 2.78/1.46  Preprocessing        : 0.32
% 2.78/1.46  Parsing              : 0.17
% 2.78/1.46  CNF conversion       : 0.02
% 3.11/1.46  Main loop            : 0.38
% 3.11/1.46  Inferencing          : 0.15
% 3.11/1.46  Reduction            : 0.13
% 3.11/1.46  Demodulation         : 0.10
% 3.11/1.46  BG Simplification    : 0.02
% 3.11/1.46  Subsumption          : 0.05
% 3.11/1.46  Abstraction          : 0.02
% 3.11/1.46  MUC search           : 0.00
% 3.11/1.46  Cooper               : 0.00
% 3.11/1.46  Total                : 0.73
% 3.11/1.46  Index Insertion      : 0.00
% 3.11/1.46  Index Deletion       : 0.00
% 3.11/1.46  Index Matching       : 0.00
% 3.11/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
