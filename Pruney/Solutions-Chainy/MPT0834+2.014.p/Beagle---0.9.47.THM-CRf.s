%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:51 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 123 expanded)
%              Number of leaves         :   41 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 181 expanded)
%              Number of equality atoms :   51 (  81 expanded)
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

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_675,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k8_relset_1(A_150,B_151,C_152,D_153) = k10_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_678,plain,(
    ! [D_153] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_153) = k10_relat_1('#skF_3',D_153) ),
    inference(resolution,[status(thm)],[c_40,c_675])).

tff(c_559,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_563,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_559])).

tff(c_60,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_101,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_105,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_120,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_120])).

tff(c_126,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_123])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_134,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_130])).

tff(c_365,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_368,plain,(
    ! [D_95] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_95) = k9_relat_1('#skF_3',D_95) ),
    inference(resolution,[status(thm)],[c_40,c_365])).

tff(c_246,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_250,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_246])).

tff(c_38,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_100,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_251,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_100])).

tff(c_369,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_251])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_369])).

tff(c_373,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_564,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_373])).

tff(c_679,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_564])).

tff(c_389,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_393,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_389])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [B_15,A_14] : k5_relat_1(k6_relat_1(B_15),k6_relat_1(A_14)) = k6_relat_1(k3_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_446,plain,(
    ! [A_114,B_115] :
      ( k5_relat_1(k6_relat_1(A_114),B_115) = B_115
      | ~ r1_tarski(k1_relat_1(B_115),A_114)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_449,plain,(
    ! [A_114,A_11] :
      ( k5_relat_1(k6_relat_1(A_114),k6_relat_1(A_11)) = k6_relat_1(A_11)
      | ~ r1_tarski(A_11,A_114)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_446])).

tff(c_452,plain,(
    ! [A_116,A_117] :
      ( k6_relat_1(k3_xboole_0(A_116,A_117)) = k6_relat_1(A_116)
      | ~ r1_tarski(A_116,A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22,c_449])).

tff(c_473,plain,(
    ! [A_116,A_117] :
      ( k3_xboole_0(A_116,A_117) = k1_relat_1(k6_relat_1(A_116))
      | ~ r1_tarski(A_116,A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_16])).

tff(c_489,plain,(
    ! [A_118,A_119] :
      ( k3_xboole_0(A_118,A_119) = A_118
      | ~ r1_tarski(A_118,A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_473])).

tff(c_523,plain,(
    ! [B_124,A_125] :
      ( k3_xboole_0(k2_relat_1(B_124),A_125) = k2_relat_1(B_124)
      | ~ v5_relat_1(B_124,A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_4,c_489])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k10_relat_1(B_7,k3_xboole_0(k2_relat_1(B_7),A_6)) = k10_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_755,plain,(
    ! [B_157,A_158] :
      ( k10_relat_1(B_157,k2_relat_1(B_157)) = k10_relat_1(B_157,A_158)
      | ~ v1_relat_1(B_157)
      | ~ v5_relat_1(B_157,A_158)
      | ~ v1_relat_1(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_10])).

tff(c_759,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_393,c_755])).

tff(c_765,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_759])).

tff(c_12,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_769,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_765,c_12])).

tff(c_776,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_769])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_679,c_776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.78  
% 3.46/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.78  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.78  
% 3.46/1.78  %Foreground sorts:
% 3.46/1.78  
% 3.46/1.78  
% 3.46/1.78  %Background operators:
% 3.46/1.78  
% 3.46/1.78  
% 3.46/1.78  %Foreground operators:
% 3.46/1.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.46/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.46/1.78  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.46/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.46/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.46/1.78  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.78  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.78  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.46/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.46/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.46/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.46/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.46/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.46/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.78  
% 3.56/1.81  tff(f_96, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.56/1.81  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.56/1.81  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.56/1.81  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.56/1.81  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.56/1.81  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.56/1.81  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.56/1.81  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.56/1.81  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.56/1.81  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.56/1.81  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.56/1.81  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.56/1.81  tff(f_63, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.56/1.81  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 3.56/1.81  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.56/1.81  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.56/1.81  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.56/1.81  tff(c_675, plain, (![A_150, B_151, C_152, D_153]: (k8_relset_1(A_150, B_151, C_152, D_153)=k10_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.81  tff(c_678, plain, (![D_153]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_153)=k10_relat_1('#skF_3', D_153))), inference(resolution, [status(thm)], [c_40, c_675])).
% 3.56/1.81  tff(c_559, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.56/1.81  tff(c_563, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_559])).
% 3.56/1.81  tff(c_60, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.56/1.81  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_60])).
% 3.56/1.81  tff(c_101, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.81  tff(c_105, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_101])).
% 3.56/1.81  tff(c_120, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.81  tff(c_123, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_120])).
% 3.56/1.81  tff(c_126, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_123])).
% 3.56/1.81  tff(c_8, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.81  tff(c_130, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 3.56/1.81  tff(c_134, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_130])).
% 3.56/1.81  tff(c_365, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.56/1.81  tff(c_368, plain, (![D_95]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_95)=k9_relat_1('#skF_3', D_95))), inference(resolution, [status(thm)], [c_40, c_365])).
% 3.56/1.81  tff(c_246, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.56/1.81  tff(c_250, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_246])).
% 3.56/1.81  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.56/1.81  tff(c_100, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.56/1.81  tff(c_251, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_100])).
% 3.56/1.81  tff(c_369, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_251])).
% 3.56/1.81  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_369])).
% 3.56/1.81  tff(c_373, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.56/1.81  tff(c_564, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_373])).
% 3.56/1.81  tff(c_679, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_564])).
% 3.56/1.81  tff(c_389, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.81  tff(c_393, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_389])).
% 3.56/1.81  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.81  tff(c_16, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.56/1.81  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.81  tff(c_22, plain, (![B_15, A_14]: (k5_relat_1(k6_relat_1(B_15), k6_relat_1(A_14))=k6_relat_1(k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.56/1.81  tff(c_446, plain, (![A_114, B_115]: (k5_relat_1(k6_relat_1(A_114), B_115)=B_115 | ~r1_tarski(k1_relat_1(B_115), A_114) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.56/1.81  tff(c_449, plain, (![A_114, A_11]: (k5_relat_1(k6_relat_1(A_114), k6_relat_1(A_11))=k6_relat_1(A_11) | ~r1_tarski(A_11, A_114) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_446])).
% 3.56/1.81  tff(c_452, plain, (![A_116, A_117]: (k6_relat_1(k3_xboole_0(A_116, A_117))=k6_relat_1(A_116) | ~r1_tarski(A_116, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_449])).
% 3.56/1.81  tff(c_473, plain, (![A_116, A_117]: (k3_xboole_0(A_116, A_117)=k1_relat_1(k6_relat_1(A_116)) | ~r1_tarski(A_116, A_117))), inference(superposition, [status(thm), theory('equality')], [c_452, c_16])).
% 3.56/1.81  tff(c_489, plain, (![A_118, A_119]: (k3_xboole_0(A_118, A_119)=A_118 | ~r1_tarski(A_118, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_473])).
% 3.56/1.81  tff(c_523, plain, (![B_124, A_125]: (k3_xboole_0(k2_relat_1(B_124), A_125)=k2_relat_1(B_124) | ~v5_relat_1(B_124, A_125) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_4, c_489])).
% 3.56/1.81  tff(c_10, plain, (![B_7, A_6]: (k10_relat_1(B_7, k3_xboole_0(k2_relat_1(B_7), A_6))=k10_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.81  tff(c_755, plain, (![B_157, A_158]: (k10_relat_1(B_157, k2_relat_1(B_157))=k10_relat_1(B_157, A_158) | ~v1_relat_1(B_157) | ~v5_relat_1(B_157, A_158) | ~v1_relat_1(B_157))), inference(superposition, [status(thm), theory('equality')], [c_523, c_10])).
% 3.56/1.81  tff(c_759, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_393, c_755])).
% 3.56/1.81  tff(c_765, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_759])).
% 3.56/1.81  tff(c_12, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.56/1.81  tff(c_769, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_765, c_12])).
% 3.56/1.81  tff(c_776, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_769])).
% 3.56/1.81  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_679, c_776])).
% 3.56/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.81  
% 3.56/1.81  Inference rules
% 3.56/1.81  ----------------------
% 3.56/1.81  #Ref     : 0
% 3.56/1.81  #Sup     : 178
% 3.56/1.81  #Fact    : 0
% 3.56/1.81  #Define  : 0
% 3.56/1.81  #Split   : 1
% 3.56/1.81  #Chain   : 0
% 3.56/1.81  #Close   : 0
% 3.56/1.81  
% 3.56/1.81  Ordering : KBO
% 3.56/1.81  
% 3.56/1.81  Simplification rules
% 3.56/1.81  ----------------------
% 3.56/1.81  #Subsume      : 16
% 3.56/1.81  #Demod        : 87
% 3.56/1.81  #Tautology    : 77
% 3.56/1.81  #SimpNegUnit  : 1
% 3.56/1.81  #BackRed      : 5
% 3.56/1.81  
% 3.56/1.81  #Partial instantiations: 0
% 3.56/1.81  #Strategies tried      : 1
% 3.56/1.81  
% 3.56/1.81  Timing (in seconds)
% 3.56/1.81  ----------------------
% 3.56/1.82  Preprocessing        : 0.46
% 3.56/1.82  Parsing              : 0.23
% 3.56/1.82  CNF conversion       : 0.03
% 3.56/1.82  Main loop            : 0.55
% 3.56/1.82  Inferencing          : 0.22
% 3.56/1.82  Reduction            : 0.17
% 3.56/1.82  Demodulation         : 0.12
% 3.56/1.82  BG Simplification    : 0.03
% 3.56/1.82  Subsumption          : 0.07
% 3.56/1.82  Abstraction          : 0.03
% 3.56/1.82  MUC search           : 0.00
% 3.56/1.82  Cooper               : 0.00
% 3.56/1.82  Total                : 1.06
% 3.56/1.82  Index Insertion      : 0.00
% 3.56/1.82  Index Deletion       : 0.00
% 3.56/1.82  Index Matching       : 0.00
% 3.56/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
