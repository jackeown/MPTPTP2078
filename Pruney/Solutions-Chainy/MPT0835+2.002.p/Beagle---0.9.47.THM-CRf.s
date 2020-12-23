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
% DateTime   : Thu Dec  3 10:07:55 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 194 expanded)
%              Number of leaves         :   40 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 335 expanded)
%              Number of equality atoms :   69 ( 130 expanded)
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

tff(f_107,negated_conjecture,(
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

tff(f_94,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1014,plain,(
    ! [B_155,A_156] :
      ( k5_relat_1(B_155,k6_relat_1(A_156)) = B_155
      | ~ r1_tarski(k2_relat_1(B_155),A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1031,plain,(
    ! [B_155] :
      ( k5_relat_1(B_155,k6_relat_1(k2_relat_1(B_155))) = B_155
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_1014])).

tff(c_16,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1139,plain,(
    ! [A_168,B_169] :
      ( k10_relat_1(A_168,k1_relat_1(B_169)) = k1_relat_1(k5_relat_1(A_168,B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1148,plain,(
    ! [A_168,A_15] :
      ( k1_relat_1(k5_relat_1(A_168,k6_relat_1(A_15))) = k10_relat_1(A_168,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1139])).

tff(c_1309,plain,(
    ! [A_179,A_180] :
      ( k1_relat_1(k5_relat_1(A_179,k6_relat_1(A_180))) = k10_relat_1(A_179,A_180)
      | ~ v1_relat_1(A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1148])).

tff(c_1342,plain,(
    ! [B_155] :
      ( k10_relat_1(B_155,k2_relat_1(B_155)) = k1_relat_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_1309])).

tff(c_1578,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1581,plain,(
    ! [D_197] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_197) = k10_relat_1('#skF_3',D_197) ),
    inference(resolution,[status(thm)],[c_48,c_1578])).

tff(c_942,plain,(
    ! [C_142,A_143,B_144] :
      ( v4_relat_1(C_142,A_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_946,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_942])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_949,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_946,c_22])).

tff(c_952,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_949])).

tff(c_972,plain,(
    ! [B_151,A_152] :
      ( k2_relat_1(k7_relat_1(B_151,A_152)) = k9_relat_1(B_151,A_152)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_990,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_972])).

tff(c_994,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_990])).

tff(c_1404,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k7_relset_1(A_184,B_185,C_186,D_187) = k9_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1407,plain,(
    ! [D_187] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_187) = k9_relat_1('#skF_3',D_187) ),
    inference(resolution,[status(thm)],[c_48,c_1404])).

tff(c_180,plain,(
    ! [B_67,A_68] :
      ( v4_relat_1(B_67,A_68)
      | ~ r1_tarski(k1_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_204,plain,(
    ! [B_71] :
      ( v4_relat_1(B_71,k1_relat_1(B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_180])).

tff(c_286,plain,(
    ! [B_81] :
      ( k7_relat_1(B_81,k1_relat_1(B_81)) = B_81
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_204,c_22])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_292,plain,(
    ! [B_81] :
      ( k9_relat_1(B_81,k1_relat_1(B_81)) = k2_relat_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_18])).

tff(c_84,plain,(
    ! [C_49,B_50,A_51] :
      ( v5_relat_1(C_49,B_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_51,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_88,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_235,plain,(
    ! [B_74,A_75] :
      ( k5_relat_1(B_74,k6_relat_1(A_75)) = B_74
      | ~ r1_tarski(k2_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_249,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_235])).

tff(c_320,plain,(
    ! [A_83,B_84] :
      ( k10_relat_1(A_83,k1_relat_1(B_84)) = k1_relat_1(k5_relat_1(A_83,B_84))
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_329,plain,(
    ! [A_83,A_15] :
      ( k1_relat_1(k5_relat_1(A_83,k6_relat_1(A_15))) = k10_relat_1(A_83,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_320])).

tff(c_496,plain,(
    ! [A_97,A_98] :
      ( k1_relat_1(k5_relat_1(A_97,k6_relat_1(A_98))) = k10_relat_1(A_97,A_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_329])).

tff(c_842,plain,(
    ! [B_126,A_127] :
      ( k10_relat_1(B_126,A_127) = k1_relat_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v5_relat_1(B_126,A_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_496])).

tff(c_854,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_842])).

tff(c_864,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_854])).

tff(c_772,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k8_relset_1(A_114,B_115,C_116,D_117) = k10_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_775,plain,(
    ! [D_117] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_117) = k10_relat_1('#skF_3',D_117) ),
    inference(resolution,[status(thm)],[c_48,c_772])).

tff(c_557,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_560,plain,(
    ! [D_103] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_103) = k9_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_48,c_557])).

tff(c_406,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_410,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_406])).

tff(c_46,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_411,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_83])).

tff(c_633,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_411])).

tff(c_776,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_633])).

tff(c_866,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_776])).

tff(c_882,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_866])).

tff(c_886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_882])).

tff(c_887,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1408,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_887])).

tff(c_1409,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_1408])).

tff(c_1582,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1409])).

tff(c_1600,plain,
    ( k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_1582])).

tff(c_1602,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_1600])).

tff(c_889,plain,(
    ! [C_131,B_132,A_133] :
      ( v5_relat_1(C_131,B_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_893,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_889])).

tff(c_1028,plain,(
    ! [B_6,A_5] :
      ( k5_relat_1(B_6,k6_relat_1(A_5)) = B_6
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_1014])).

tff(c_1681,plain,(
    ! [B_205,A_206] :
      ( k10_relat_1(B_205,A_206) = k1_relat_1(B_205)
      | ~ v1_relat_1(B_205)
      | ~ v5_relat_1(B_205,A_206)
      | ~ v1_relat_1(B_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_1309])).

tff(c_1693,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_893,c_1681])).

tff(c_1703,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1693])).

tff(c_1704,plain,(
    ! [A_207,B_208,C_209] :
      ( k8_relset_1(A_207,B_208,C_209,B_208) = k1_relset_1(A_207,B_208,C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1706,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1704])).

tff(c_1708,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1706])).

tff(c_1731,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1703,c_1708])).

tff(c_1732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1602,c_1731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.72  
% 3.28/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.72  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.28/1.72  
% 3.28/1.72  %Foreground sorts:
% 3.28/1.72  
% 3.28/1.72  
% 3.28/1.72  %Background operators:
% 3.28/1.72  
% 3.28/1.72  
% 3.28/1.72  %Foreground operators:
% 3.28/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.72  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.28/1.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.28/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.28/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.28/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.28/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.72  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.28/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.72  
% 3.28/1.74  tff(f_107, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.28/1.74  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.74  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.28/1.74  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.28/1.74  tff(f_66, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.28/1.74  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.28/1.74  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.28/1.74  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.74  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.28/1.74  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.28/1.74  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.28/1.74  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.28/1.74  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.28/1.74  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.28/1.74  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.28/1.74  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.28/1.74  tff(c_70, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.28/1.74  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_70])).
% 3.28/1.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.74  tff(c_1014, plain, (![B_155, A_156]: (k5_relat_1(B_155, k6_relat_1(A_156))=B_155 | ~r1_tarski(k2_relat_1(B_155), A_156) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.28/1.74  tff(c_1031, plain, (![B_155]: (k5_relat_1(B_155, k6_relat_1(k2_relat_1(B_155)))=B_155 | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_6, c_1014])).
% 3.28/1.74  tff(c_16, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.74  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.74  tff(c_1139, plain, (![A_168, B_169]: (k10_relat_1(A_168, k1_relat_1(B_169))=k1_relat_1(k5_relat_1(A_168, B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.74  tff(c_1148, plain, (![A_168, A_15]: (k1_relat_1(k5_relat_1(A_168, k6_relat_1(A_15)))=k10_relat_1(A_168, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_168))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1139])).
% 3.28/1.74  tff(c_1309, plain, (![A_179, A_180]: (k1_relat_1(k5_relat_1(A_179, k6_relat_1(A_180)))=k10_relat_1(A_179, A_180) | ~v1_relat_1(A_179))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1148])).
% 3.28/1.74  tff(c_1342, plain, (![B_155]: (k10_relat_1(B_155, k2_relat_1(B_155))=k1_relat_1(B_155) | ~v1_relat_1(B_155) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_1031, c_1309])).
% 3.28/1.74  tff(c_1578, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.28/1.74  tff(c_1581, plain, (![D_197]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_197)=k10_relat_1('#skF_3', D_197))), inference(resolution, [status(thm)], [c_48, c_1578])).
% 3.28/1.74  tff(c_942, plain, (![C_142, A_143, B_144]: (v4_relat_1(C_142, A_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.28/1.74  tff(c_946, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_942])).
% 3.28/1.74  tff(c_22, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.28/1.74  tff(c_949, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_946, c_22])).
% 3.28/1.74  tff(c_952, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_949])).
% 3.28/1.74  tff(c_972, plain, (![B_151, A_152]: (k2_relat_1(k7_relat_1(B_151, A_152))=k9_relat_1(B_151, A_152) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.74  tff(c_990, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_952, c_972])).
% 3.28/1.74  tff(c_994, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_990])).
% 3.28/1.74  tff(c_1404, plain, (![A_184, B_185, C_186, D_187]: (k7_relset_1(A_184, B_185, C_186, D_187)=k9_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.28/1.74  tff(c_1407, plain, (![D_187]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_187)=k9_relat_1('#skF_3', D_187))), inference(resolution, [status(thm)], [c_48, c_1404])).
% 3.28/1.74  tff(c_180, plain, (![B_67, A_68]: (v4_relat_1(B_67, A_68) | ~r1_tarski(k1_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.74  tff(c_204, plain, (![B_71]: (v4_relat_1(B_71, k1_relat_1(B_71)) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_6, c_180])).
% 3.28/1.74  tff(c_286, plain, (![B_81]: (k7_relat_1(B_81, k1_relat_1(B_81))=B_81 | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_204, c_22])).
% 3.28/1.74  tff(c_18, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.74  tff(c_292, plain, (![B_81]: (k9_relat_1(B_81, k1_relat_1(B_81))=k2_relat_1(B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_286, c_18])).
% 3.28/1.74  tff(c_84, plain, (![C_49, B_50, A_51]: (v5_relat_1(C_49, B_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_51, B_50))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.28/1.74  tff(c_88, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_84])).
% 3.28/1.74  tff(c_14, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.74  tff(c_235, plain, (![B_74, A_75]: (k5_relat_1(B_74, k6_relat_1(A_75))=B_74 | ~r1_tarski(k2_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.28/1.74  tff(c_249, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_14, c_235])).
% 3.28/1.74  tff(c_320, plain, (![A_83, B_84]: (k10_relat_1(A_83, k1_relat_1(B_84))=k1_relat_1(k5_relat_1(A_83, B_84)) | ~v1_relat_1(B_84) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.74  tff(c_329, plain, (![A_83, A_15]: (k1_relat_1(k5_relat_1(A_83, k6_relat_1(A_15)))=k10_relat_1(A_83, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_24, c_320])).
% 3.28/1.74  tff(c_496, plain, (![A_97, A_98]: (k1_relat_1(k5_relat_1(A_97, k6_relat_1(A_98)))=k10_relat_1(A_97, A_98) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_329])).
% 3.28/1.74  tff(c_842, plain, (![B_126, A_127]: (k10_relat_1(B_126, A_127)=k1_relat_1(B_126) | ~v1_relat_1(B_126) | ~v5_relat_1(B_126, A_127) | ~v1_relat_1(B_126))), inference(superposition, [status(thm), theory('equality')], [c_249, c_496])).
% 3.28/1.74  tff(c_854, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_842])).
% 3.28/1.74  tff(c_864, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_854])).
% 3.28/1.74  tff(c_772, plain, (![A_114, B_115, C_116, D_117]: (k8_relset_1(A_114, B_115, C_116, D_117)=k10_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.28/1.74  tff(c_775, plain, (![D_117]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_117)=k10_relat_1('#skF_3', D_117))), inference(resolution, [status(thm)], [c_48, c_772])).
% 3.28/1.74  tff(c_557, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.28/1.74  tff(c_560, plain, (![D_103]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_103)=k9_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_48, c_557])).
% 3.28/1.74  tff(c_406, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.28/1.74  tff(c_410, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_406])).
% 3.28/1.74  tff(c_46, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.28/1.74  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.28/1.74  tff(c_411, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_83])).
% 3.28/1.74  tff(c_633, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_411])).
% 3.28/1.74  tff(c_776, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_775, c_633])).
% 3.28/1.74  tff(c_866, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_864, c_776])).
% 3.28/1.74  tff(c_882, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_292, c_866])).
% 3.28/1.74  tff(c_886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_882])).
% 3.28/1.74  tff(c_887, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.28/1.74  tff(c_1408, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1407, c_887])).
% 3.28/1.74  tff(c_1409, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_994, c_1408])).
% 3.28/1.74  tff(c_1582, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1409])).
% 3.28/1.74  tff(c_1600, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1342, c_1582])).
% 3.28/1.74  tff(c_1602, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_1600])).
% 3.28/1.74  tff(c_889, plain, (![C_131, B_132, A_133]: (v5_relat_1(C_131, B_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.28/1.74  tff(c_893, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_889])).
% 3.28/1.74  tff(c_1028, plain, (![B_6, A_5]: (k5_relat_1(B_6, k6_relat_1(A_5))=B_6 | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(resolution, [status(thm)], [c_14, c_1014])).
% 3.28/1.74  tff(c_1681, plain, (![B_205, A_206]: (k10_relat_1(B_205, A_206)=k1_relat_1(B_205) | ~v1_relat_1(B_205) | ~v5_relat_1(B_205, A_206) | ~v1_relat_1(B_205))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_1309])).
% 3.28/1.74  tff(c_1693, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_893, c_1681])).
% 3.28/1.74  tff(c_1703, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1693])).
% 3.28/1.74  tff(c_1704, plain, (![A_207, B_208, C_209]: (k8_relset_1(A_207, B_208, C_209, B_208)=k1_relset_1(A_207, B_208, C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.28/1.74  tff(c_1706, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1704])).
% 3.28/1.74  tff(c_1708, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1706])).
% 3.28/1.74  tff(c_1731, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1703, c_1708])).
% 3.28/1.74  tff(c_1732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1602, c_1731])).
% 3.28/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.74  
% 3.28/1.74  Inference rules
% 3.28/1.74  ----------------------
% 3.28/1.74  #Ref     : 0
% 3.28/1.74  #Sup     : 357
% 3.28/1.74  #Fact    : 0
% 3.28/1.74  #Define  : 0
% 3.28/1.74  #Split   : 1
% 3.28/1.74  #Chain   : 0
% 3.28/1.74  #Close   : 0
% 3.28/1.74  
% 3.28/1.74  Ordering : KBO
% 3.28/1.74  
% 3.28/1.74  Simplification rules
% 3.28/1.74  ----------------------
% 3.28/1.74  #Subsume      : 10
% 3.28/1.74  #Demod        : 298
% 3.28/1.74  #Tautology    : 210
% 3.28/1.74  #SimpNegUnit  : 1
% 3.28/1.74  #BackRed      : 11
% 3.28/1.74  
% 3.28/1.74  #Partial instantiations: 0
% 3.28/1.74  #Strategies tried      : 1
% 3.28/1.74  
% 3.28/1.74  Timing (in seconds)
% 3.28/1.74  ----------------------
% 3.28/1.74  Preprocessing        : 0.34
% 3.28/1.74  Parsing              : 0.15
% 3.28/1.74  CNF conversion       : 0.02
% 3.28/1.74  Main loop            : 0.44
% 3.28/1.74  Inferencing          : 0.17
% 3.28/1.74  Reduction            : 0.14
% 3.28/1.74  Demodulation         : 0.10
% 3.28/1.74  BG Simplification    : 0.04
% 3.28/1.74  Subsumption          : 0.07
% 3.28/1.74  Abstraction          : 0.03
% 3.28/1.74  MUC search           : 0.00
% 3.28/1.74  Cooper               : 0.00
% 3.28/1.74  Total                : 0.82
% 3.28/1.74  Index Insertion      : 0.00
% 3.28/1.74  Index Deletion       : 0.00
% 3.28/1.74  Index Matching       : 0.00
% 3.28/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
