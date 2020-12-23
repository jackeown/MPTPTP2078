%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 157 expanded)
%              Number of leaves         :   45 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 231 expanded)
%              Number of equality atoms :   63 ( 107 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_868,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k8_relset_1(A_138,B_139,C_140,D_141) = k10_relat_1(C_140,D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_875,plain,(
    ! [D_141] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_141) = k10_relat_1('#skF_3',D_141) ),
    inference(resolution,[status(thm)],[c_48,c_868])).

tff(c_742,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_746,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_742])).

tff(c_124,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_124])).

tff(c_130,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_130])).

tff(c_170,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_173,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_170])).

tff(c_176,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_173])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_180,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_6])).

tff(c_184,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_180])).

tff(c_513,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k7_relset_1(A_97,B_98,C_99,D_100) = k9_relat_1(C_99,D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_520,plain,(
    ! [D_100] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_100) = k9_relat_1('#skF_3',D_100) ),
    inference(resolution,[status(thm)],[c_48,c_513])).

tff(c_269,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_273,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_269])).

tff(c_46,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_129,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_274,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_129])).

tff(c_521,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_274])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_521])).

tff(c_525,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_747,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_525])).

tff(c_876,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_747])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30] :
      ( m1_subset_1(k3_relset_1(A_28,B_29,C_30),k1_zfmisc_1(k2_zfmisc_1(B_29,A_28)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_616,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_620,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_616])).

tff(c_1030,plain,(
    ! [B_155,A_156,C_157] :
      ( k1_relset_1(B_155,A_156,k3_relset_1(A_156,B_155,C_157)) = k2_relset_1(A_156,B_155,C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_156,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1037,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1030])).

tff(c_1041,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_1037])).

tff(c_30,plain,(
    ! [A_25,B_26,C_27] :
      ( m1_subset_1(k1_relset_1(A_25,B_26,C_27),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1045,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k3_relset_1('#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_30])).

tff(c_1109,plain,(
    ~ m1_subset_1(k3_relset_1('#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1045])).

tff(c_1112,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_32,c_1109])).

tff(c_1116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1112])).

tff(c_1117,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1045])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [B_18,A_17] : k5_relat_1(k6_relat_1(B_18),k6_relat_1(A_17)) = k6_relat_1(k3_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_645,plain,(
    ! [B_122,A_123] :
      ( k9_relat_1(B_122,k2_relat_1(A_123)) = k2_relat_1(k5_relat_1(A_123,B_122))
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_657,plain,(
    ! [A_14,B_122] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_14),B_122)) = k9_relat_1(B_122,A_14)
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_645])).

tff(c_662,plain,(
    ! [A_124,B_125] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_124),B_125)) = k9_relat_1(B_125,A_124)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_657])).

tff(c_680,plain,(
    ! [A_17,B_18] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_17,B_18))) = k9_relat_1(k6_relat_1(A_17),B_18)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_662])).

tff(c_684,plain,(
    ! [A_17,B_18] : k9_relat_1(k6_relat_1(A_17),B_18) = k3_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18,c_680])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k9_relat_1(k6_relat_1(A_15),B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_685,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_20])).

tff(c_1122,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1117,c_685])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_591,plain,(
    ! [B_115,A_116] :
      ( k10_relat_1(B_115,k3_xboole_0(k2_relat_1(B_115),A_116)) = k10_relat_1(B_115,A_116)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_604,plain,(
    ! [B_115,B_2] :
      ( k10_relat_1(B_115,k3_xboole_0(B_2,k2_relat_1(B_115))) = k10_relat_1(B_115,B_2)
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_591])).

tff(c_1126,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_604])).

tff(c_1136,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1126])).

tff(c_12,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1143,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_12])).

tff(c_1150,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1143])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.70  
% 3.24/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.70  %$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.70  
% 3.24/1.70  %Foreground sorts:
% 3.24/1.70  
% 3.24/1.70  
% 3.24/1.70  %Background operators:
% 3.24/1.70  
% 3.24/1.70  
% 3.24/1.70  %Foreground operators:
% 3.24/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.24/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.24/1.70  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.24/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.24/1.70  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.24/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.70  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.24/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.24/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.24/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.24/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.24/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.24/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.24/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.24/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.71  
% 3.24/1.72  tff(f_111, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.24/1.72  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.24/1.72  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.72  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.72  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.72  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.24/1.72  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.24/1.72  tff(f_94, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.24/1.72  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.24/1.72  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.24/1.72  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 3.24/1.72  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.24/1.72  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.24/1.72  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.24/1.72  tff(f_64, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.24/1.72  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.24/1.72  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.24/1.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.24/1.72  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.24/1.72  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.24/1.72  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.24/1.72  tff(c_868, plain, (![A_138, B_139, C_140, D_141]: (k8_relset_1(A_138, B_139, C_140, D_141)=k10_relat_1(C_140, D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.24/1.72  tff(c_875, plain, (![D_141]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_141)=k10_relat_1('#skF_3', D_141))), inference(resolution, [status(thm)], [c_48, c_868])).
% 3.24/1.72  tff(c_742, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.24/1.72  tff(c_746, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_742])).
% 3.24/1.72  tff(c_124, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.24/1.72  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_124])).
% 3.24/1.72  tff(c_130, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.24/1.72  tff(c_134, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_130])).
% 3.24/1.72  tff(c_170, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.24/1.72  tff(c_173, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_170])).
% 3.24/1.72  tff(c_176, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_173])).
% 3.24/1.72  tff(c_6, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.72  tff(c_180, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_176, c_6])).
% 3.24/1.72  tff(c_184, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_180])).
% 3.24/1.72  tff(c_513, plain, (![A_97, B_98, C_99, D_100]: (k7_relset_1(A_97, B_98, C_99, D_100)=k9_relat_1(C_99, D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.24/1.72  tff(c_520, plain, (![D_100]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_100)=k9_relat_1('#skF_3', D_100))), inference(resolution, [status(thm)], [c_48, c_513])).
% 3.24/1.72  tff(c_269, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.24/1.72  tff(c_273, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_269])).
% 3.24/1.72  tff(c_46, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.24/1.72  tff(c_129, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.24/1.72  tff(c_274, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_129])).
% 3.24/1.72  tff(c_521, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_274])).
% 3.24/1.72  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_521])).
% 3.24/1.72  tff(c_525, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 3.24/1.72  tff(c_747, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_746, c_525])).
% 3.24/1.72  tff(c_876, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_875, c_747])).
% 3.24/1.72  tff(c_32, plain, (![A_28, B_29, C_30]: (m1_subset_1(k3_relset_1(A_28, B_29, C_30), k1_zfmisc_1(k2_zfmisc_1(B_29, A_28))) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.24/1.72  tff(c_616, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.24/1.72  tff(c_620, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_616])).
% 3.24/1.72  tff(c_1030, plain, (![B_155, A_156, C_157]: (k1_relset_1(B_155, A_156, k3_relset_1(A_156, B_155, C_157))=k2_relset_1(A_156, B_155, C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_156, B_155))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.24/1.72  tff(c_1037, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1030])).
% 3.24/1.72  tff(c_1041, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_1037])).
% 3.24/1.72  tff(c_30, plain, (![A_25, B_26, C_27]: (m1_subset_1(k1_relset_1(A_25, B_26, C_27), k1_zfmisc_1(A_25)) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.24/1.72  tff(c_1045, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k3_relset_1('#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1041, c_30])).
% 3.24/1.72  tff(c_1109, plain, (~m1_subset_1(k3_relset_1('#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1045])).
% 3.24/1.72  tff(c_1112, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_32, c_1109])).
% 3.24/1.72  tff(c_1116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1112])).
% 3.24/1.72  tff(c_1117, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1045])).
% 3.24/1.72  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.24/1.72  tff(c_18, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.72  tff(c_22, plain, (![B_18, A_17]: (k5_relat_1(k6_relat_1(B_18), k6_relat_1(A_17))=k6_relat_1(k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.24/1.72  tff(c_645, plain, (![B_122, A_123]: (k9_relat_1(B_122, k2_relat_1(A_123))=k2_relat_1(k5_relat_1(A_123, B_122)) | ~v1_relat_1(B_122) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.24/1.72  tff(c_657, plain, (![A_14, B_122]: (k2_relat_1(k5_relat_1(k6_relat_1(A_14), B_122))=k9_relat_1(B_122, A_14) | ~v1_relat_1(B_122) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_645])).
% 3.24/1.72  tff(c_662, plain, (![A_124, B_125]: (k2_relat_1(k5_relat_1(k6_relat_1(A_124), B_125))=k9_relat_1(B_125, A_124) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_657])).
% 3.24/1.72  tff(c_680, plain, (![A_17, B_18]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_17, B_18)))=k9_relat_1(k6_relat_1(A_17), B_18) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_662])).
% 3.24/1.72  tff(c_684, plain, (![A_17, B_18]: (k9_relat_1(k6_relat_1(A_17), B_18)=k3_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18, c_680])).
% 3.24/1.72  tff(c_20, plain, (![A_15, B_16]: (k9_relat_1(k6_relat_1(A_15), B_16)=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.72  tff(c_685, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_684, c_20])).
% 3.24/1.72  tff(c_1122, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1117, c_685])).
% 3.24/1.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.72  tff(c_591, plain, (![B_115, A_116]: (k10_relat_1(B_115, k3_xboole_0(k2_relat_1(B_115), A_116))=k10_relat_1(B_115, A_116) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.72  tff(c_604, plain, (![B_115, B_2]: (k10_relat_1(B_115, k3_xboole_0(B_2, k2_relat_1(B_115)))=k10_relat_1(B_115, B_2) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_2, c_591])).
% 3.24/1.72  tff(c_1126, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1122, c_604])).
% 3.24/1.72  tff(c_1136, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1126])).
% 3.24/1.72  tff(c_12, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.24/1.72  tff(c_1143, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1136, c_12])).
% 3.24/1.72  tff(c_1150, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1143])).
% 3.24/1.72  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_876, c_1150])).
% 3.24/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.72  
% 3.24/1.72  Inference rules
% 3.24/1.72  ----------------------
% 3.24/1.72  #Ref     : 0
% 3.24/1.72  #Sup     : 277
% 3.24/1.72  #Fact    : 0
% 3.24/1.72  #Define  : 0
% 3.24/1.72  #Split   : 2
% 3.24/1.72  #Chain   : 0
% 3.24/1.72  #Close   : 0
% 3.24/1.72  
% 3.24/1.72  Ordering : KBO
% 3.24/1.72  
% 3.24/1.72  Simplification rules
% 3.24/1.72  ----------------------
% 3.24/1.72  #Subsume      : 7
% 3.24/1.72  #Demod        : 109
% 3.24/1.72  #Tautology    : 161
% 3.24/1.72  #SimpNegUnit  : 1
% 3.24/1.72  #BackRed      : 7
% 3.24/1.72  
% 3.24/1.72  #Partial instantiations: 0
% 3.24/1.72  #Strategies tried      : 1
% 3.24/1.72  
% 3.24/1.72  Timing (in seconds)
% 3.24/1.72  ----------------------
% 3.24/1.73  Preprocessing        : 0.46
% 3.24/1.73  Parsing              : 0.27
% 3.24/1.73  CNF conversion       : 0.02
% 3.24/1.73  Main loop            : 0.44
% 3.24/1.73  Inferencing          : 0.16
% 3.24/1.73  Reduction            : 0.14
% 3.24/1.73  Demodulation         : 0.11
% 3.24/1.73  BG Simplification    : 0.03
% 3.24/1.73  Subsumption          : 0.07
% 3.24/1.73  Abstraction          : 0.02
% 3.24/1.73  MUC search           : 0.00
% 3.24/1.73  Cooper               : 0.00
% 3.24/1.73  Total                : 0.94
% 3.24/1.73  Index Insertion      : 0.00
% 3.24/1.73  Index Deletion       : 0.00
% 3.24/1.73  Index Matching       : 0.00
% 3.24/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
