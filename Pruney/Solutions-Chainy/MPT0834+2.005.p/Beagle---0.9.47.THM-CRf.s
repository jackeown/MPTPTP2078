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
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 134 expanded)
%              Number of leaves         :   45 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 189 expanded)
%              Number of equality atoms :   58 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_815,plain,(
    ! [C_117,A_118,B_119] :
      ( v1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_819,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_815])).

tff(c_924,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_928,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_924])).

tff(c_1256,plain,(
    ! [A_159,B_160,C_161] :
      ( m1_subset_1(k2_relset_1(A_159,B_160,C_161),k1_zfmisc_1(B_160))
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1279,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_1256])).

tff(c_1286,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1279])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [B_21,A_20] : k5_relat_1(k6_relat_1(B_21),k6_relat_1(A_20)) = k6_relat_1(k3_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1035,plain,(
    ! [B_148,A_149] :
      ( k9_relat_1(B_148,k2_relat_1(A_149)) = k2_relat_1(k5_relat_1(A_149,B_148))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1047,plain,(
    ! [A_13,B_148] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_13),B_148)) = k9_relat_1(B_148,A_13)
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1035])).

tff(c_1052,plain,(
    ! [A_150,B_151] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_150),B_151)) = k9_relat_1(B_151,A_150)
      | ~ v1_relat_1(B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1047])).

tff(c_1073,plain,(
    ! [A_20,B_21] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_20,B_21))) = k9_relat_1(k6_relat_1(A_20),B_21)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1052])).

tff(c_1077,plain,(
    ! [A_20,B_21] : k9_relat_1(k6_relat_1(A_20),B_21) = k3_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_1073])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( k9_relat_1(k6_relat_1(A_18),B_19) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1288,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = B_163
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_162)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_28])).

tff(c_1298,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1286,c_1288])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_871,plain,(
    ! [B_134,A_135] :
      ( k10_relat_1(B_134,k3_xboole_0(k2_relat_1(B_134),A_135)) = k10_relat_1(B_134,A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_884,plain,(
    ! [B_134,B_2] :
      ( k10_relat_1(B_134,k3_xboole_0(B_2,k2_relat_1(B_134))) = k10_relat_1(B_134,B_2)
      | ~ v1_relat_1(B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_871])).

tff(c_1305,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1298,c_884])).

tff(c_1309,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_1305])).

tff(c_10,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1314,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1309,c_10])).

tff(c_1321,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_1314])).

tff(c_1480,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k8_relset_1(A_173,B_174,C_175,D_176) = k10_relat_1(C_175,D_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1487,plain,(
    ! [D_176] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_176) = k10_relat_1('#skF_3',D_176) ),
    inference(resolution,[status(thm)],[c_52,c_1480])).

tff(c_1025,plain,(
    ! [A_145,B_146,C_147] :
      ( k1_relset_1(A_145,B_146,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1029,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1025])).

tff(c_141,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_145,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_141])).

tff(c_181,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_185,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_181])).

tff(c_186,plain,(
    ! [B_71,A_72] :
      ( k7_relat_1(B_71,A_72) = B_71
      | ~ v4_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_189,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_186])).

tff(c_192,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_189])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_4])).

tff(c_200,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_196])).

tff(c_792,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_relset_1(A_112,B_113,C_114,D_115) = k9_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_799,plain,(
    ! [D_115] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_115) = k9_relat_1('#skF_3',D_115) ),
    inference(resolution,[status(thm)],[c_52,c_792])).

tff(c_286,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_290,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_286])).

tff(c_50,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_131,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_291,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_131])).

tff(c_800,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_291])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_800])).

tff(c_804,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1030,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1029,c_804])).

tff(c_1488,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1030])).

tff(c_1491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.54  
% 3.60/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.54  %$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.60/1.54  
% 3.60/1.54  %Foreground sorts:
% 3.60/1.54  
% 3.60/1.54  
% 3.60/1.54  %Background operators:
% 3.60/1.54  
% 3.60/1.54  
% 3.60/1.54  %Foreground operators:
% 3.60/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.60/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.60/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.60/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.60/1.54  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.60/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.60/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.54  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.60/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.60/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.60/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.60/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.60/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.60/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.60/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.60/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.54  
% 3.60/1.56  tff(f_117, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.60/1.56  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.60/1.56  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.60/1.56  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.60/1.56  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.60/1.56  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.60/1.56  tff(f_78, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.60/1.56  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.60/1.56  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.60/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.60/1.56  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.60/1.56  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.60/1.56  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.60/1.56  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.60/1.56  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.60/1.56  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.60/1.56  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.60/1.56  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.60/1.56  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.60/1.56  tff(c_815, plain, (![C_117, A_118, B_119]: (v1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.60/1.56  tff(c_819, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_815])).
% 3.60/1.56  tff(c_924, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.60/1.56  tff(c_928, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_924])).
% 3.60/1.56  tff(c_1256, plain, (![A_159, B_160, C_161]: (m1_subset_1(k2_relset_1(A_159, B_160, C_161), k1_zfmisc_1(B_160)) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.60/1.56  tff(c_1279, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_928, c_1256])).
% 3.60/1.56  tff(c_1286, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1279])).
% 3.60/1.56  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.60/1.56  tff(c_16, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.56  tff(c_30, plain, (![B_21, A_20]: (k5_relat_1(k6_relat_1(B_21), k6_relat_1(A_20))=k6_relat_1(k3_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.60/1.56  tff(c_1035, plain, (![B_148, A_149]: (k9_relat_1(B_148, k2_relat_1(A_149))=k2_relat_1(k5_relat_1(A_149, B_148)) | ~v1_relat_1(B_148) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.60/1.56  tff(c_1047, plain, (![A_13, B_148]: (k2_relat_1(k5_relat_1(k6_relat_1(A_13), B_148))=k9_relat_1(B_148, A_13) | ~v1_relat_1(B_148) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1035])).
% 3.60/1.56  tff(c_1052, plain, (![A_150, B_151]: (k2_relat_1(k5_relat_1(k6_relat_1(A_150), B_151))=k9_relat_1(B_151, A_150) | ~v1_relat_1(B_151))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1047])).
% 3.60/1.56  tff(c_1073, plain, (![A_20, B_21]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_20, B_21)))=k9_relat_1(k6_relat_1(A_20), B_21) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1052])).
% 3.60/1.56  tff(c_1077, plain, (![A_20, B_21]: (k9_relat_1(k6_relat_1(A_20), B_21)=k3_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_1073])).
% 3.60/1.56  tff(c_28, plain, (![A_18, B_19]: (k9_relat_1(k6_relat_1(A_18), B_19)=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.60/1.56  tff(c_1288, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=B_163 | ~m1_subset_1(B_163, k1_zfmisc_1(A_162)))), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_28])).
% 3.60/1.56  tff(c_1298, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1286, c_1288])).
% 3.60/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.60/1.56  tff(c_871, plain, (![B_134, A_135]: (k10_relat_1(B_134, k3_xboole_0(k2_relat_1(B_134), A_135))=k10_relat_1(B_134, A_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.56  tff(c_884, plain, (![B_134, B_2]: (k10_relat_1(B_134, k3_xboole_0(B_2, k2_relat_1(B_134)))=k10_relat_1(B_134, B_2) | ~v1_relat_1(B_134))), inference(superposition, [status(thm), theory('equality')], [c_2, c_871])).
% 3.60/1.56  tff(c_1305, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1298, c_884])).
% 3.60/1.56  tff(c_1309, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_1305])).
% 3.60/1.56  tff(c_10, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.60/1.56  tff(c_1314, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1309, c_10])).
% 3.60/1.56  tff(c_1321, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_1314])).
% 3.60/1.56  tff(c_1480, plain, (![A_173, B_174, C_175, D_176]: (k8_relset_1(A_173, B_174, C_175, D_176)=k10_relat_1(C_175, D_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.60/1.56  tff(c_1487, plain, (![D_176]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_176)=k10_relat_1('#skF_3', D_176))), inference(resolution, [status(thm)], [c_52, c_1480])).
% 3.60/1.56  tff(c_1025, plain, (![A_145, B_146, C_147]: (k1_relset_1(A_145, B_146, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.60/1.56  tff(c_1029, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_1025])).
% 3.60/1.56  tff(c_141, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.60/1.56  tff(c_145, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_141])).
% 3.60/1.56  tff(c_181, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.60/1.56  tff(c_185, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_181])).
% 3.60/1.56  tff(c_186, plain, (![B_71, A_72]: (k7_relat_1(B_71, A_72)=B_71 | ~v4_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.60/1.56  tff(c_189, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_186])).
% 3.60/1.56  tff(c_192, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_189])).
% 3.60/1.56  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.56  tff(c_196, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_192, c_4])).
% 3.60/1.56  tff(c_200, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_196])).
% 3.60/1.56  tff(c_792, plain, (![A_112, B_113, C_114, D_115]: (k7_relset_1(A_112, B_113, C_114, D_115)=k9_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.60/1.56  tff(c_799, plain, (![D_115]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_115)=k9_relat_1('#skF_3', D_115))), inference(resolution, [status(thm)], [c_52, c_792])).
% 3.60/1.56  tff(c_286, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.60/1.56  tff(c_290, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_286])).
% 3.60/1.56  tff(c_50, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.60/1.56  tff(c_131, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.60/1.56  tff(c_291, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_131])).
% 3.60/1.56  tff(c_800, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_291])).
% 3.60/1.56  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_800])).
% 3.60/1.56  tff(c_804, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.60/1.56  tff(c_1030, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1029, c_804])).
% 3.60/1.56  tff(c_1488, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1030])).
% 3.60/1.56  tff(c_1491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1321, c_1488])).
% 3.60/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.56  
% 3.60/1.56  Inference rules
% 3.60/1.56  ----------------------
% 3.60/1.56  #Ref     : 0
% 3.60/1.56  #Sup     : 341
% 3.60/1.56  #Fact    : 0
% 3.60/1.56  #Define  : 0
% 3.60/1.56  #Split   : 1
% 3.60/1.56  #Chain   : 0
% 3.60/1.56  #Close   : 0
% 3.60/1.56  
% 3.60/1.56  Ordering : KBO
% 3.60/1.56  
% 3.60/1.56  Simplification rules
% 3.60/1.56  ----------------------
% 3.60/1.56  #Subsume      : 6
% 3.60/1.56  #Demod        : 231
% 3.60/1.56  #Tautology    : 234
% 3.60/1.56  #SimpNegUnit  : 0
% 3.60/1.56  #BackRed      : 13
% 3.60/1.56  
% 3.60/1.56  #Partial instantiations: 0
% 3.60/1.56  #Strategies tried      : 1
% 3.60/1.56  
% 3.60/1.56  Timing (in seconds)
% 3.60/1.56  ----------------------
% 3.60/1.56  Preprocessing        : 0.34
% 3.60/1.56  Parsing              : 0.19
% 3.60/1.56  CNF conversion       : 0.02
% 3.60/1.56  Main loop            : 0.44
% 3.60/1.56  Inferencing          : 0.16
% 3.60/1.56  Reduction            : 0.16
% 3.60/1.56  Demodulation         : 0.13
% 3.60/1.56  BG Simplification    : 0.03
% 3.60/1.56  Subsumption          : 0.06
% 3.60/1.56  Abstraction          : 0.02
% 3.60/1.56  MUC search           : 0.00
% 3.60/1.56  Cooper               : 0.00
% 3.60/1.56  Total                : 0.82
% 3.60/1.56  Index Insertion      : 0.00
% 3.60/1.56  Index Deletion       : 0.00
% 3.60/1.56  Index Matching       : 0.00
% 3.60/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
