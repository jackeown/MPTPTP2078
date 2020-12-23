%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:55 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 156 expanded)
%              Number of leaves         :   40 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 255 expanded)
%              Number of equality atoms :   60 ( 102 expanded)
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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_76,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_72,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1187,plain,(
    ! [B_167,A_168] :
      ( k5_relat_1(B_167,k6_relat_1(A_168)) = B_167
      | ~ r1_tarski(k2_relat_1(B_167),A_168)
      | ~ v1_relat_1(B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1204,plain,(
    ! [B_167] :
      ( k5_relat_1(B_167,k6_relat_1(k2_relat_1(B_167))) = B_167
      | ~ v1_relat_1(B_167) ) ),
    inference(resolution,[status(thm)],[c_6,c_1187])).

tff(c_16,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1205,plain,(
    ! [A_169,B_170] :
      ( k10_relat_1(A_169,k1_relat_1(B_170)) = k1_relat_1(k5_relat_1(A_169,B_170))
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1214,plain,(
    ! [A_169,A_15] :
      ( k1_relat_1(k5_relat_1(A_169,k6_relat_1(A_15))) = k10_relat_1(A_169,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1205])).

tff(c_1245,plain,(
    ! [A_173,A_174] :
      ( k1_relat_1(k5_relat_1(A_173,k6_relat_1(A_174))) = k10_relat_1(A_173,A_174)
      | ~ v1_relat_1(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1214])).

tff(c_1275,plain,(
    ! [B_167] :
      ( k10_relat_1(B_167,k2_relat_1(B_167)) = k1_relat_1(B_167)
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_1245])).

tff(c_1765,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k8_relset_1(A_207,B_208,C_209,D_210) = k10_relat_1(C_209,D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1768,plain,(
    ! [D_210] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_210) = k10_relat_1('#skF_3',D_210) ),
    inference(resolution,[status(thm)],[c_46,c_1765])).

tff(c_1074,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1078,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1074])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1081,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1078,c_22])).

tff(c_1084,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1081])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1088,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_18])).

tff(c_1092,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1088])).

tff(c_1613,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k7_relset_1(A_196,B_197,C_198,D_199) = k9_relat_1(C_198,D_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1616,plain,(
    ! [D_199] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_199) = k9_relat_1('#skF_3',D_199) ),
    inference(resolution,[status(thm)],[c_46,c_1613])).

tff(c_1433,plain,(
    ! [A_185,B_186,C_187] :
      ( k1_relset_1(A_185,B_186,C_187) = k1_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1437,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1433])).

tff(c_131,plain,(
    ! [B_64,A_65] :
      ( v4_relat_1(B_64,A_65)
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [B_66] :
      ( v4_relat_1(B_66,k1_relat_1(B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_242,plain,(
    ! [B_76] :
      ( k7_relat_1(B_76,k1_relat_1(B_76)) = B_76
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_146,c_22])).

tff(c_248,plain,(
    ! [B_76] :
      ( k9_relat_1(B_76,k1_relat_1(B_76)) = k2_relat_1(B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_18])).

tff(c_90,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_94,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_90])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_346,plain,(
    ! [B_84,A_85] :
      ( k5_relat_1(B_84,k6_relat_1(A_85)) = B_84
      | ~ r1_tarski(k2_relat_1(B_84),A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_360,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_346])).

tff(c_421,plain,(
    ! [A_90,B_91] :
      ( k10_relat_1(A_90,k1_relat_1(B_91)) = k1_relat_1(k5_relat_1(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_430,plain,(
    ! [A_90,A_15] :
      ( k1_relat_1(k5_relat_1(A_90,k6_relat_1(A_15))) = k10_relat_1(A_90,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_421])).

tff(c_484,plain,(
    ! [A_94,A_95] :
      ( k1_relat_1(k5_relat_1(A_94,k6_relat_1(A_95))) = k10_relat_1(A_94,A_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_430])).

tff(c_840,plain,(
    ! [B_126,A_127] :
      ( k10_relat_1(B_126,A_127) = k1_relat_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v5_relat_1(B_126,A_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_484])).

tff(c_852,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_840])).

tff(c_862,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_852])).

tff(c_807,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k8_relset_1(A_119,B_120,C_121,D_122) = k10_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_810,plain,(
    ! [D_122] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_122) = k10_relat_1('#skF_3',D_122) ),
    inference(resolution,[status(thm)],[c_46,c_807])).

tff(c_768,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_relset_1(A_112,B_113,C_114,D_115) = k9_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_771,plain,(
    ! [D_115] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_115) = k9_relat_1('#skF_3',D_115) ),
    inference(resolution,[status(thm)],[c_46,c_768])).

tff(c_608,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_612,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_608])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_89,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_613,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_89])).

tff(c_772,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_613])).

tff(c_811,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_772])).

tff(c_863,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_811])).

tff(c_894,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_863])).

tff(c_898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_894])).

tff(c_899,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1438,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_899])).

tff(c_1617,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1438])).

tff(c_1618,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1617])).

tff(c_1770,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1768,c_1618])).

tff(c_1801,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_1770])).

tff(c_1805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.58  
% 3.43/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.58  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.43/1.58  
% 3.43/1.58  %Foreground sorts:
% 3.43/1.58  
% 3.43/1.58  
% 3.43/1.58  %Background operators:
% 3.43/1.58  
% 3.43/1.58  
% 3.43/1.58  %Foreground operators:
% 3.43/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.43/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.43/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.43/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.43/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.43/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.43/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.43/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.43/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.58  
% 3.43/1.60  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.43/1.60  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.43/1.60  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.43/1.60  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.43/1.60  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.43/1.60  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.43/1.60  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.43/1.60  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.43/1.60  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.43/1.60  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.43/1.60  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.43/1.60  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.43/1.60  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.43/1.60  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.43/1.60  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.43/1.60  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.43/1.60  tff(c_68, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.43/1.60  tff(c_72, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_68])).
% 3.43/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.60  tff(c_1187, plain, (![B_167, A_168]: (k5_relat_1(B_167, k6_relat_1(A_168))=B_167 | ~r1_tarski(k2_relat_1(B_167), A_168) | ~v1_relat_1(B_167))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.60  tff(c_1204, plain, (![B_167]: (k5_relat_1(B_167, k6_relat_1(k2_relat_1(B_167)))=B_167 | ~v1_relat_1(B_167))), inference(resolution, [status(thm)], [c_6, c_1187])).
% 3.43/1.60  tff(c_16, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.43/1.60  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.43/1.60  tff(c_1205, plain, (![A_169, B_170]: (k10_relat_1(A_169, k1_relat_1(B_170))=k1_relat_1(k5_relat_1(A_169, B_170)) | ~v1_relat_1(B_170) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.43/1.60  tff(c_1214, plain, (![A_169, A_15]: (k1_relat_1(k5_relat_1(A_169, k6_relat_1(A_15)))=k10_relat_1(A_169, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_169))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1205])).
% 3.43/1.60  tff(c_1245, plain, (![A_173, A_174]: (k1_relat_1(k5_relat_1(A_173, k6_relat_1(A_174)))=k10_relat_1(A_173, A_174) | ~v1_relat_1(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1214])).
% 3.43/1.60  tff(c_1275, plain, (![B_167]: (k10_relat_1(B_167, k2_relat_1(B_167))=k1_relat_1(B_167) | ~v1_relat_1(B_167) | ~v1_relat_1(B_167))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_1245])).
% 3.43/1.60  tff(c_1765, plain, (![A_207, B_208, C_209, D_210]: (k8_relset_1(A_207, B_208, C_209, D_210)=k10_relat_1(C_209, D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.43/1.60  tff(c_1768, plain, (![D_210]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_210)=k10_relat_1('#skF_3', D_210))), inference(resolution, [status(thm)], [c_46, c_1765])).
% 3.43/1.60  tff(c_1074, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.60  tff(c_1078, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1074])).
% 3.43/1.60  tff(c_22, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.43/1.60  tff(c_1081, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1078, c_22])).
% 3.43/1.60  tff(c_1084, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1081])).
% 3.43/1.60  tff(c_18, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.43/1.60  tff(c_1088, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1084, c_18])).
% 3.43/1.60  tff(c_1092, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1088])).
% 3.43/1.60  tff(c_1613, plain, (![A_196, B_197, C_198, D_199]: (k7_relset_1(A_196, B_197, C_198, D_199)=k9_relat_1(C_198, D_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.43/1.60  tff(c_1616, plain, (![D_199]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_199)=k9_relat_1('#skF_3', D_199))), inference(resolution, [status(thm)], [c_46, c_1613])).
% 3.43/1.60  tff(c_1433, plain, (![A_185, B_186, C_187]: (k1_relset_1(A_185, B_186, C_187)=k1_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.43/1.60  tff(c_1437, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1433])).
% 3.43/1.60  tff(c_131, plain, (![B_64, A_65]: (v4_relat_1(B_64, A_65) | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.60  tff(c_146, plain, (![B_66]: (v4_relat_1(B_66, k1_relat_1(B_66)) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_6, c_131])).
% 3.43/1.60  tff(c_242, plain, (![B_76]: (k7_relat_1(B_76, k1_relat_1(B_76))=B_76 | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_146, c_22])).
% 3.43/1.60  tff(c_248, plain, (![B_76]: (k9_relat_1(B_76, k1_relat_1(B_76))=k2_relat_1(B_76) | ~v1_relat_1(B_76) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_242, c_18])).
% 3.43/1.60  tff(c_90, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.60  tff(c_94, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_90])).
% 3.43/1.60  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.60  tff(c_346, plain, (![B_84, A_85]: (k5_relat_1(B_84, k6_relat_1(A_85))=B_84 | ~r1_tarski(k2_relat_1(B_84), A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.60  tff(c_360, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_14, c_346])).
% 3.43/1.60  tff(c_421, plain, (![A_90, B_91]: (k10_relat_1(A_90, k1_relat_1(B_91))=k1_relat_1(k5_relat_1(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.43/1.60  tff(c_430, plain, (![A_90, A_15]: (k1_relat_1(k5_relat_1(A_90, k6_relat_1(A_15)))=k10_relat_1(A_90, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_24, c_421])).
% 3.43/1.60  tff(c_484, plain, (![A_94, A_95]: (k1_relat_1(k5_relat_1(A_94, k6_relat_1(A_95)))=k10_relat_1(A_94, A_95) | ~v1_relat_1(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_430])).
% 3.43/1.60  tff(c_840, plain, (![B_126, A_127]: (k10_relat_1(B_126, A_127)=k1_relat_1(B_126) | ~v1_relat_1(B_126) | ~v5_relat_1(B_126, A_127) | ~v1_relat_1(B_126))), inference(superposition, [status(thm), theory('equality')], [c_360, c_484])).
% 3.43/1.60  tff(c_852, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_840])).
% 3.43/1.60  tff(c_862, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_852])).
% 3.43/1.60  tff(c_807, plain, (![A_119, B_120, C_121, D_122]: (k8_relset_1(A_119, B_120, C_121, D_122)=k10_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.43/1.60  tff(c_810, plain, (![D_122]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_122)=k10_relat_1('#skF_3', D_122))), inference(resolution, [status(thm)], [c_46, c_807])).
% 3.43/1.60  tff(c_768, plain, (![A_112, B_113, C_114, D_115]: (k7_relset_1(A_112, B_113, C_114, D_115)=k9_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.43/1.60  tff(c_771, plain, (![D_115]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_115)=k9_relat_1('#skF_3', D_115))), inference(resolution, [status(thm)], [c_46, c_768])).
% 3.43/1.60  tff(c_608, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.43/1.60  tff(c_612, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_608])).
% 3.43/1.60  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.43/1.60  tff(c_89, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.43/1.60  tff(c_613, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_89])).
% 3.43/1.60  tff(c_772, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_613])).
% 3.43/1.60  tff(c_811, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_810, c_772])).
% 3.43/1.60  tff(c_863, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_811])).
% 3.43/1.60  tff(c_894, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_248, c_863])).
% 3.43/1.60  tff(c_898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_894])).
% 3.43/1.60  tff(c_899, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.43/1.60  tff(c_1438, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_899])).
% 3.43/1.60  tff(c_1617, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1438])).
% 3.43/1.60  tff(c_1618, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1617])).
% 3.43/1.60  tff(c_1770, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1768, c_1618])).
% 3.43/1.60  tff(c_1801, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1275, c_1770])).
% 3.43/1.60  tff(c_1805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_1801])).
% 3.43/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  Inference rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Ref     : 0
% 3.43/1.60  #Sup     : 371
% 3.43/1.60  #Fact    : 0
% 3.43/1.60  #Define  : 0
% 3.43/1.60  #Split   : 1
% 3.43/1.60  #Chain   : 0
% 3.43/1.60  #Close   : 0
% 3.43/1.60  
% 3.43/1.60  Ordering : KBO
% 3.43/1.60  
% 3.43/1.60  Simplification rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Subsume      : 14
% 3.43/1.60  #Demod        : 325
% 3.43/1.60  #Tautology    : 209
% 3.43/1.60  #SimpNegUnit  : 0
% 3.43/1.60  #BackRed      : 10
% 3.43/1.60  
% 3.43/1.60  #Partial instantiations: 0
% 3.43/1.60  #Strategies tried      : 1
% 3.43/1.60  
% 3.43/1.60  Timing (in seconds)
% 3.43/1.60  ----------------------
% 3.43/1.60  Preprocessing        : 0.34
% 3.43/1.60  Parsing              : 0.18
% 3.43/1.60  CNF conversion       : 0.02
% 3.43/1.60  Main loop            : 0.49
% 3.43/1.60  Inferencing          : 0.19
% 3.43/1.60  Reduction            : 0.15
% 3.43/1.60  Demodulation         : 0.11
% 3.43/1.60  BG Simplification    : 0.03
% 3.43/1.60  Subsumption          : 0.08
% 3.43/1.60  Abstraction          : 0.03
% 3.43/1.60  MUC search           : 0.00
% 3.43/1.60  Cooper               : 0.00
% 3.43/1.60  Total                : 0.87
% 3.43/1.60  Index Insertion      : 0.00
% 3.43/1.60  Index Deletion       : 0.00
% 3.43/1.60  Index Matching       : 0.00
% 3.43/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
