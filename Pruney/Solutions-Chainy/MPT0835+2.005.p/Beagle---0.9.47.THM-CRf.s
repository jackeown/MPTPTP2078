%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:56 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 147 expanded)
%              Number of leaves         :   40 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 232 expanded)
%              Number of equality atoms :   60 (  97 expanded)
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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_74,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_89,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_843,plain,(
    ! [B_133,A_134] :
      ( k5_relat_1(B_133,k6_relat_1(A_134)) = B_133
      | ~ r1_tarski(k2_relat_1(B_133),A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_860,plain,(
    ! [B_133] :
      ( k5_relat_1(B_133,k6_relat_1(k2_relat_1(B_133))) = B_133
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_843])).

tff(c_12,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_995,plain,(
    ! [A_147,B_148] :
      ( k10_relat_1(A_147,k1_relat_1(B_148)) = k1_relat_1(k5_relat_1(A_147,B_148))
      | ~ v1_relat_1(B_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1004,plain,(
    ! [A_147,A_14] :
      ( k1_relat_1(k5_relat_1(A_147,k6_relat_1(A_14))) = k10_relat_1(A_147,A_14)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_995])).

tff(c_1035,plain,(
    ! [A_154,A_155] :
      ( k1_relat_1(k5_relat_1(A_154,k6_relat_1(A_155))) = k10_relat_1(A_154,A_155)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1004])).

tff(c_1153,plain,(
    ! [B_164] :
      ( k10_relat_1(B_164,k2_relat_1(B_164)) = k1_relat_1(B_164)
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_1035])).

tff(c_1066,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k8_relset_1(A_156,B_157,C_158,D_159) = k10_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1069,plain,(
    ! [D_159] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_159) = k10_relat_1('#skF_3',D_159) ),
    inference(resolution,[status(thm)],[c_44,c_1066])).

tff(c_752,plain,(
    ! [C_118,A_119,B_120] :
      ( v4_relat_1(C_118,A_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_756,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_752])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_770,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_756,c_20])).

tff(c_773,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_770])).

tff(c_820,plain,(
    ! [B_131,A_132] :
      ( k2_relat_1(k7_relat_1(B_131,A_132)) = k9_relat_1(B_131,A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_838,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_820])).

tff(c_842,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_838])).

tff(c_1009,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k7_relset_1(A_149,B_150,C_151,D_152) = k9_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1012,plain,(
    ! [D_152] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_152) = k9_relat_1('#skF_3',D_152) ),
    inference(resolution,[status(thm)],[c_44,c_1009])).

tff(c_971,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_975,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_971])).

tff(c_14,plain,(
    ! [A_6] :
      ( k9_relat_1(A_6,k1_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_699,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k7_relset_1(A_106,B_107,C_108,D_109) = k9_relat_1(C_108,D_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_702,plain,(
    ! [D_109] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_109) = k9_relat_1('#skF_3',D_109) ),
    inference(resolution,[status(thm)],[c_44,c_699])).

tff(c_103,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_107,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_195,plain,(
    ! [B_68,A_69] :
      ( k5_relat_1(B_68,k6_relat_1(A_69)) = B_68
      | ~ r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_209,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_342,plain,(
    ! [A_82,B_83] :
      ( k10_relat_1(A_82,k1_relat_1(B_83)) = k1_relat_1(k5_relat_1(A_82,B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_351,plain,(
    ! [A_82,A_14] :
      ( k1_relat_1(k5_relat_1(A_82,k6_relat_1(A_14))) = k10_relat_1(A_82,A_14)
      | ~ v1_relat_1(k6_relat_1(A_14))
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_342])).

tff(c_356,plain,(
    ! [A_84,A_85] :
      ( k1_relat_1(k5_relat_1(A_84,k6_relat_1(A_85))) = k10_relat_1(A_84,A_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_351])).

tff(c_577,plain,(
    ! [B_100,A_101] :
      ( k10_relat_1(B_100,A_101) = k1_relat_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v5_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_356])).

tff(c_589,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_577])).

tff(c_599,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_589])).

tff(c_563,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k8_relset_1(A_95,B_96,C_97,D_98) = k10_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_566,plain,(
    ! [D_98] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_98) = k10_relat_1('#skF_3',D_98) ),
    inference(resolution,[status(thm)],[c_44,c_563])).

tff(c_332,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_336,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_332])).

tff(c_42,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_94,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_337,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_94])).

tff(c_567,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_337])).

tff(c_600,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_567])).

tff(c_720,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_600])).

tff(c_732,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_720])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_732])).

tff(c_737,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_976,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_737])).

tff(c_1013,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_976])).

tff(c_1014,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_1013])).

tff(c_1092,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_1014])).

tff(c_1163,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_1092])).

tff(c_1183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.45  
% 2.85/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.45  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.85/1.45  
% 2.85/1.45  %Foreground sorts:
% 2.85/1.45  
% 2.85/1.45  
% 2.85/1.45  %Background operators:
% 2.85/1.45  
% 2.85/1.45  
% 2.85/1.45  %Foreground operators:
% 2.85/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.85/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.85/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.85/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.85/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.85/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.85/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.85/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.85/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.85/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.85/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.45  
% 3.12/1.47  tff(f_103, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.12/1.47  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.12/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.12/1.47  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.12/1.47  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.12/1.47  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.12/1.47  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.12/1.47  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.12/1.47  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.12/1.47  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.12/1.47  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.12/1.47  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.12/1.47  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.12/1.47  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.12/1.47  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.12/1.47  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.12/1.47  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.12/1.47  tff(c_89, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.12/1.47  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_89])).
% 3.12/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.47  tff(c_843, plain, (![B_133, A_134]: (k5_relat_1(B_133, k6_relat_1(A_134))=B_133 | ~r1_tarski(k2_relat_1(B_133), A_134) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.12/1.47  tff(c_860, plain, (![B_133]: (k5_relat_1(B_133, k6_relat_1(k2_relat_1(B_133)))=B_133 | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_6, c_843])).
% 3.12/1.47  tff(c_12, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.47  tff(c_22, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.12/1.47  tff(c_995, plain, (![A_147, B_148]: (k10_relat_1(A_147, k1_relat_1(B_148))=k1_relat_1(k5_relat_1(A_147, B_148)) | ~v1_relat_1(B_148) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.47  tff(c_1004, plain, (![A_147, A_14]: (k1_relat_1(k5_relat_1(A_147, k6_relat_1(A_14)))=k10_relat_1(A_147, A_14) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_22, c_995])).
% 3.12/1.47  tff(c_1035, plain, (![A_154, A_155]: (k1_relat_1(k5_relat_1(A_154, k6_relat_1(A_155)))=k10_relat_1(A_154, A_155) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1004])).
% 3.12/1.47  tff(c_1153, plain, (![B_164]: (k10_relat_1(B_164, k2_relat_1(B_164))=k1_relat_1(B_164) | ~v1_relat_1(B_164) | ~v1_relat_1(B_164))), inference(superposition, [status(thm), theory('equality')], [c_860, c_1035])).
% 3.12/1.47  tff(c_1066, plain, (![A_156, B_157, C_158, D_159]: (k8_relset_1(A_156, B_157, C_158, D_159)=k10_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.47  tff(c_1069, plain, (![D_159]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_159)=k10_relat_1('#skF_3', D_159))), inference(resolution, [status(thm)], [c_44, c_1066])).
% 3.12/1.47  tff(c_752, plain, (![C_118, A_119, B_120]: (v4_relat_1(C_118, A_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.12/1.47  tff(c_756, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_752])).
% 3.12/1.47  tff(c_20, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.12/1.47  tff(c_770, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_756, c_20])).
% 3.12/1.47  tff(c_773, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_770])).
% 3.12/1.47  tff(c_820, plain, (![B_131, A_132]: (k2_relat_1(k7_relat_1(B_131, A_132))=k9_relat_1(B_131, A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.12/1.47  tff(c_838, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_773, c_820])).
% 3.12/1.47  tff(c_842, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_838])).
% 3.12/1.47  tff(c_1009, plain, (![A_149, B_150, C_151, D_152]: (k7_relset_1(A_149, B_150, C_151, D_152)=k9_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.47  tff(c_1012, plain, (![D_152]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_152)=k9_relat_1('#skF_3', D_152))), inference(resolution, [status(thm)], [c_44, c_1009])).
% 3.12/1.47  tff(c_971, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.12/1.47  tff(c_975, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_971])).
% 3.12/1.47  tff(c_14, plain, (![A_6]: (k9_relat_1(A_6, k1_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.12/1.47  tff(c_699, plain, (![A_106, B_107, C_108, D_109]: (k7_relset_1(A_106, B_107, C_108, D_109)=k9_relat_1(C_108, D_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.12/1.47  tff(c_702, plain, (![D_109]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_109)=k9_relat_1('#skF_3', D_109))), inference(resolution, [status(thm)], [c_44, c_699])).
% 3.12/1.47  tff(c_103, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.12/1.47  tff(c_107, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_103])).
% 3.12/1.47  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.47  tff(c_195, plain, (![B_68, A_69]: (k5_relat_1(B_68, k6_relat_1(A_69))=B_68 | ~r1_tarski(k2_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.12/1.47  tff(c_209, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_10, c_195])).
% 3.12/1.47  tff(c_342, plain, (![A_82, B_83]: (k10_relat_1(A_82, k1_relat_1(B_83))=k1_relat_1(k5_relat_1(A_82, B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.47  tff(c_351, plain, (![A_82, A_14]: (k1_relat_1(k5_relat_1(A_82, k6_relat_1(A_14)))=k10_relat_1(A_82, A_14) | ~v1_relat_1(k6_relat_1(A_14)) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_22, c_342])).
% 3.12/1.47  tff(c_356, plain, (![A_84, A_85]: (k1_relat_1(k5_relat_1(A_84, k6_relat_1(A_85)))=k10_relat_1(A_84, A_85) | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_351])).
% 3.12/1.47  tff(c_577, plain, (![B_100, A_101]: (k10_relat_1(B_100, A_101)=k1_relat_1(B_100) | ~v1_relat_1(B_100) | ~v5_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_209, c_356])).
% 3.12/1.47  tff(c_589, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_107, c_577])).
% 3.12/1.47  tff(c_599, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_589])).
% 3.12/1.47  tff(c_563, plain, (![A_95, B_96, C_97, D_98]: (k8_relset_1(A_95, B_96, C_97, D_98)=k10_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.12/1.47  tff(c_566, plain, (![D_98]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_98)=k10_relat_1('#skF_3', D_98))), inference(resolution, [status(thm)], [c_44, c_563])).
% 3.12/1.47  tff(c_332, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.12/1.47  tff(c_336, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_332])).
% 3.12/1.47  tff(c_42, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.12/1.47  tff(c_94, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.12/1.47  tff(c_337, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_94])).
% 3.12/1.47  tff(c_567, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_337])).
% 3.12/1.47  tff(c_600, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_567])).
% 3.12/1.47  tff(c_720, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_600])).
% 3.12/1.47  tff(c_732, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_720])).
% 3.12/1.47  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_732])).
% 3.12/1.47  tff(c_737, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.12/1.47  tff(c_976, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_975, c_737])).
% 3.12/1.47  tff(c_1013, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1012, c_976])).
% 3.12/1.47  tff(c_1014, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_1013])).
% 3.12/1.47  tff(c_1092, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_1014])).
% 3.12/1.47  tff(c_1163, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_1092])).
% 3.12/1.47  tff(c_1183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_1163])).
% 3.12/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.47  
% 3.12/1.47  Inference rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Ref     : 0
% 3.12/1.47  #Sup     : 246
% 3.12/1.47  #Fact    : 0
% 3.12/1.47  #Define  : 0
% 3.12/1.47  #Split   : 1
% 3.12/1.47  #Chain   : 0
% 3.12/1.47  #Close   : 0
% 3.12/1.47  
% 3.12/1.47  Ordering : KBO
% 3.12/1.47  
% 3.12/1.47  Simplification rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Subsume      : 7
% 3.12/1.47  #Demod        : 188
% 3.12/1.47  #Tautology    : 149
% 3.12/1.47  #SimpNegUnit  : 0
% 3.12/1.47  #BackRed      : 10
% 3.12/1.47  
% 3.12/1.47  #Partial instantiations: 0
% 3.12/1.47  #Strategies tried      : 1
% 3.12/1.47  
% 3.12/1.47  Timing (in seconds)
% 3.12/1.47  ----------------------
% 3.12/1.47  Preprocessing        : 0.31
% 3.12/1.47  Parsing              : 0.17
% 3.12/1.47  CNF conversion       : 0.02
% 3.12/1.47  Main loop            : 0.38
% 3.12/1.47  Inferencing          : 0.15
% 3.12/1.47  Reduction            : 0.12
% 3.12/1.47  Demodulation         : 0.09
% 3.12/1.47  BG Simplification    : 0.02
% 3.12/1.47  Subsumption          : 0.05
% 3.12/1.47  Abstraction          : 0.02
% 3.12/1.47  MUC search           : 0.00
% 3.12/1.47  Cooper               : 0.00
% 3.12/1.47  Total                : 0.73
% 3.12/1.47  Index Insertion      : 0.00
% 3.12/1.47  Index Deletion       : 0.00
% 3.12/1.47  Index Matching       : 0.00
% 3.12/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
