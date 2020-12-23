%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:54 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 234 expanded)
%              Number of leaves         :   44 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 400 expanded)
%              Number of equality atoms :   59 ( 118 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_103,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1443,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k8_relset_1(A_209,B_210,C_211,D_212) = k10_relat_1(C_211,D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1449,plain,(
    ! [D_212] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_212) = k10_relat_1('#skF_3',D_212) ),
    inference(resolution,[status(thm)],[c_46,c_1443])).

tff(c_1030,plain,(
    ! [A_169,B_170,C_171] :
      ( k1_relset_1(A_169,B_170,C_171) = k1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1039,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1030])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_127,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_135,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_127])).

tff(c_243,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,A_82) = B_81
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_249,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_243])).

tff(c_255,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_249])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_259,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_12])).

tff(c_263,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_259])).

tff(c_694,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_relset_1(A_121,B_122,C_123,D_124) = k9_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_701,plain,(
    ! [D_124] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_124) = k9_relat_1('#skF_3',D_124) ),
    inference(resolution,[status(thm)],[c_46,c_694])).

tff(c_530,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_539,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_530])).

tff(c_44,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_95,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_552,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_95])).

tff(c_702,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_552])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_702])).

tff(c_706,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1049,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1039,c_706])).

tff(c_1450,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_1049])).

tff(c_761,plain,(
    ! [C_136,B_137,A_138] :
      ( v5_relat_1(C_136,B_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_769,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_761])).

tff(c_850,plain,(
    ! [C_150,A_151,B_152] :
      ( v4_relat_1(C_150,A_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_858,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_850])).

tff(c_860,plain,(
    ! [B_154,A_155] :
      ( k7_relat_1(B_154,A_155) = B_154
      | ~ v4_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_866,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_858,c_860])).

tff(c_872,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_866])).

tff(c_876,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_12])).

tff(c_880,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_876])).

tff(c_733,plain,(
    ! [B_128,A_129] :
      ( r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v5_relat_1(B_128,A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1555,plain,(
    ! [B_223,A_224,A_225] :
      ( r1_tarski(k9_relat_1(B_223,A_224),A_225)
      | ~ v5_relat_1(k7_relat_1(B_223,A_224),A_225)
      | ~ v1_relat_1(k7_relat_1(B_223,A_224))
      | ~ v1_relat_1(B_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_733])).

tff(c_1561,plain,(
    ! [A_225] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_225)
      | ~ v5_relat_1('#skF_3',A_225)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_1555])).

tff(c_1576,plain,(
    ! [A_226] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_226)
      | ~ v5_relat_1('#skF_3',A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_872,c_880,c_1561])).

tff(c_22,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_806,plain,(
    ! [B_144,A_145] : k5_relat_1(k6_relat_1(B_144),k6_relat_1(A_145)) = k6_relat_1(k3_xboole_0(A_145,B_144)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_812,plain,(
    ! [A_145,B_144] :
      ( k7_relat_1(k6_relat_1(A_145),B_144) = k6_relat_1(k3_xboole_0(A_145,B_144))
      | ~ v1_relat_1(k6_relat_1(A_145)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_26])).

tff(c_822,plain,(
    ! [A_145,B_144] : k7_relat_1(k6_relat_1(A_145),B_144) = k6_relat_1(k3_xboole_0(A_145,B_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_812])).

tff(c_42,plain,(
    ! [A_42] : m1_subset_1(k6_relat_1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_857,plain,(
    ! [A_42] : v4_relat_1(k6_relat_1(A_42),A_42) ),
    inference(resolution,[status(thm)],[c_42,c_850])).

tff(c_980,plain,(
    ! [C_160,B_161,A_162] :
      ( v4_relat_1(C_160,B_161)
      | ~ v4_relat_1(C_160,A_162)
      | ~ v1_relat_1(C_160)
      | ~ r1_tarski(A_162,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_982,plain,(
    ! [A_42,B_161] :
      ( v4_relat_1(k6_relat_1(A_42),B_161)
      | ~ v1_relat_1(k6_relat_1(A_42))
      | ~ r1_tarski(A_42,B_161) ) ),
    inference(resolution,[status(thm)],[c_857,c_980])).

tff(c_1003,plain,(
    ! [A_164,B_165] :
      ( v4_relat_1(k6_relat_1(A_164),B_165)
      | ~ r1_tarski(A_164,B_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_982])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1008,plain,(
    ! [A_164,B_165] :
      ( k7_relat_1(k6_relat_1(A_164),B_165) = k6_relat_1(A_164)
      | ~ v1_relat_1(k6_relat_1(A_164))
      | ~ r1_tarski(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_1003,c_18])).

tff(c_1061,plain,(
    ! [A_175,B_176] :
      ( k6_relat_1(k3_xboole_0(A_175,B_176)) = k6_relat_1(A_175)
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_822,c_1008])).

tff(c_1106,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(A_175,B_176) = k1_relat_1(k6_relat_1(A_175))
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1061,c_22])).

tff(c_1123,plain,(
    ! [A_175,B_176] :
      ( k3_xboole_0(A_175,B_176) = A_175
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1106])).

tff(c_1598,plain,(
    ! [A_227] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_227) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_227) ) ),
    inference(resolution,[status(thm)],[c_1576,c_1123])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k3_xboole_0(k2_relat_1(B_12),A_11)) = k10_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1632,plain,(
    ! [A_227] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_227)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1598,c_14])).

tff(c_1739,plain,(
    ! [A_231] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_231)
      | ~ v5_relat_1('#skF_3',A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1632])).

tff(c_1749,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_769,c_1739])).

tff(c_16,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1754,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_16])).

tff(c_1761,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1754])).

tff(c_1763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1450,c_1761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.71  
% 3.47/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.71  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.47/1.71  
% 3.47/1.71  %Foreground sorts:
% 3.47/1.71  
% 3.47/1.71  
% 3.47/1.71  %Background operators:
% 3.47/1.71  
% 3.47/1.71  
% 3.47/1.71  %Foreground operators:
% 3.47/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.47/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.47/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.47/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.47/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.47/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.47/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.47/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.47/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.47/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.47/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.47/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.47/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.71  
% 3.86/1.73  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.86/1.73  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.86/1.73  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.86/1.73  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.86/1.73  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.86/1.73  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.86/1.73  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.86/1.73  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.86/1.73  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.86/1.73  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.86/1.73  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.86/1.73  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.86/1.73  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.86/1.73  tff(f_79, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.86/1.73  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.86/1.73  tff(f_103, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.86/1.73  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 3.86/1.73  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.86/1.73  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.86/1.73  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.86/1.73  tff(c_1443, plain, (![A_209, B_210, C_211, D_212]: (k8_relset_1(A_209, B_210, C_211, D_212)=k10_relat_1(C_211, D_212) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.86/1.73  tff(c_1449, plain, (![D_212]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_212)=k10_relat_1('#skF_3', D_212))), inference(resolution, [status(thm)], [c_46, c_1443])).
% 3.86/1.73  tff(c_1030, plain, (![A_169, B_170, C_171]: (k1_relset_1(A_169, B_170, C_171)=k1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.86/1.73  tff(c_1039, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1030])).
% 3.86/1.73  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.86/1.73  tff(c_68, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.86/1.73  tff(c_74, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_68])).
% 3.86/1.73  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_74])).
% 3.86/1.73  tff(c_127, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.73  tff(c_135, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_127])).
% 3.86/1.73  tff(c_243, plain, (![B_81, A_82]: (k7_relat_1(B_81, A_82)=B_81 | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.86/1.73  tff(c_249, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_243])).
% 3.86/1.73  tff(c_255, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_249])).
% 3.86/1.73  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.86/1.73  tff(c_259, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_255, c_12])).
% 3.86/1.73  tff(c_263, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_259])).
% 3.86/1.73  tff(c_694, plain, (![A_121, B_122, C_123, D_124]: (k7_relset_1(A_121, B_122, C_123, D_124)=k9_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.86/1.73  tff(c_701, plain, (![D_124]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_124)=k9_relat_1('#skF_3', D_124))), inference(resolution, [status(thm)], [c_46, c_694])).
% 3.86/1.73  tff(c_530, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.86/1.73  tff(c_539, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_530])).
% 3.86/1.73  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.86/1.73  tff(c_95, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.86/1.73  tff(c_552, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_95])).
% 3.86/1.73  tff(c_702, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_701, c_552])).
% 3.86/1.73  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_263, c_702])).
% 3.86/1.73  tff(c_706, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.86/1.73  tff(c_1049, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1039, c_706])).
% 3.86/1.73  tff(c_1450, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1449, c_1049])).
% 3.86/1.73  tff(c_761, plain, (![C_136, B_137, A_138]: (v5_relat_1(C_136, B_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.73  tff(c_769, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_761])).
% 3.86/1.73  tff(c_850, plain, (![C_150, A_151, B_152]: (v4_relat_1(C_150, A_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.73  tff(c_858, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_850])).
% 3.86/1.73  tff(c_860, plain, (![B_154, A_155]: (k7_relat_1(B_154, A_155)=B_154 | ~v4_relat_1(B_154, A_155) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.86/1.73  tff(c_866, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_858, c_860])).
% 3.86/1.73  tff(c_872, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_866])).
% 3.86/1.73  tff(c_876, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_872, c_12])).
% 3.86/1.73  tff(c_880, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_876])).
% 3.86/1.73  tff(c_733, plain, (![B_128, A_129]: (r1_tarski(k2_relat_1(B_128), A_129) | ~v5_relat_1(B_128, A_129) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.86/1.73  tff(c_1555, plain, (![B_223, A_224, A_225]: (r1_tarski(k9_relat_1(B_223, A_224), A_225) | ~v5_relat_1(k7_relat_1(B_223, A_224), A_225) | ~v1_relat_1(k7_relat_1(B_223, A_224)) | ~v1_relat_1(B_223))), inference(superposition, [status(thm), theory('equality')], [c_12, c_733])).
% 3.86/1.73  tff(c_1561, plain, (![A_225]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_225) | ~v5_relat_1('#skF_3', A_225) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_872, c_1555])).
% 3.86/1.73  tff(c_1576, plain, (![A_226]: (r1_tarski(k2_relat_1('#skF_3'), A_226) | ~v5_relat_1('#skF_3', A_226))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_872, c_880, c_1561])).
% 3.86/1.73  tff(c_22, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.86/1.73  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.86/1.73  tff(c_806, plain, (![B_144, A_145]: (k5_relat_1(k6_relat_1(B_144), k6_relat_1(A_145))=k6_relat_1(k3_xboole_0(A_145, B_144)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.86/1.73  tff(c_26, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.86/1.73  tff(c_812, plain, (![A_145, B_144]: (k7_relat_1(k6_relat_1(A_145), B_144)=k6_relat_1(k3_xboole_0(A_145, B_144)) | ~v1_relat_1(k6_relat_1(A_145)))), inference(superposition, [status(thm), theory('equality')], [c_806, c_26])).
% 3.86/1.73  tff(c_822, plain, (![A_145, B_144]: (k7_relat_1(k6_relat_1(A_145), B_144)=k6_relat_1(k3_xboole_0(A_145, B_144)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_812])).
% 3.86/1.73  tff(c_42, plain, (![A_42]: (m1_subset_1(k6_relat_1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.86/1.73  tff(c_857, plain, (![A_42]: (v4_relat_1(k6_relat_1(A_42), A_42))), inference(resolution, [status(thm)], [c_42, c_850])).
% 3.86/1.73  tff(c_980, plain, (![C_160, B_161, A_162]: (v4_relat_1(C_160, B_161) | ~v4_relat_1(C_160, A_162) | ~v1_relat_1(C_160) | ~r1_tarski(A_162, B_161))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.86/1.73  tff(c_982, plain, (![A_42, B_161]: (v4_relat_1(k6_relat_1(A_42), B_161) | ~v1_relat_1(k6_relat_1(A_42)) | ~r1_tarski(A_42, B_161))), inference(resolution, [status(thm)], [c_857, c_980])).
% 3.86/1.73  tff(c_1003, plain, (![A_164, B_165]: (v4_relat_1(k6_relat_1(A_164), B_165) | ~r1_tarski(A_164, B_165))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_982])).
% 3.86/1.73  tff(c_18, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.86/1.73  tff(c_1008, plain, (![A_164, B_165]: (k7_relat_1(k6_relat_1(A_164), B_165)=k6_relat_1(A_164) | ~v1_relat_1(k6_relat_1(A_164)) | ~r1_tarski(A_164, B_165))), inference(resolution, [status(thm)], [c_1003, c_18])).
% 3.86/1.73  tff(c_1061, plain, (![A_175, B_176]: (k6_relat_1(k3_xboole_0(A_175, B_176))=k6_relat_1(A_175) | ~r1_tarski(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_822, c_1008])).
% 3.86/1.73  tff(c_1106, plain, (![A_175, B_176]: (k3_xboole_0(A_175, B_176)=k1_relat_1(k6_relat_1(A_175)) | ~r1_tarski(A_175, B_176))), inference(superposition, [status(thm), theory('equality')], [c_1061, c_22])).
% 3.86/1.73  tff(c_1123, plain, (![A_175, B_176]: (k3_xboole_0(A_175, B_176)=A_175 | ~r1_tarski(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1106])).
% 3.86/1.73  tff(c_1598, plain, (![A_227]: (k3_xboole_0(k2_relat_1('#skF_3'), A_227)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_227))), inference(resolution, [status(thm)], [c_1576, c_1123])).
% 3.86/1.73  tff(c_14, plain, (![B_12, A_11]: (k10_relat_1(B_12, k3_xboole_0(k2_relat_1(B_12), A_11))=k10_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.86/1.73  tff(c_1632, plain, (![A_227]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_227) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_227))), inference(superposition, [status(thm), theory('equality')], [c_1598, c_14])).
% 3.86/1.73  tff(c_1739, plain, (![A_231]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_231) | ~v5_relat_1('#skF_3', A_231))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1632])).
% 3.86/1.73  tff(c_1749, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_769, c_1739])).
% 3.86/1.73  tff(c_16, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.73  tff(c_1754, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1749, c_16])).
% 3.86/1.73  tff(c_1761, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1754])).
% 3.86/1.73  tff(c_1763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1450, c_1761])).
% 3.86/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.73  
% 3.86/1.73  Inference rules
% 3.86/1.73  ----------------------
% 3.86/1.73  #Ref     : 0
% 3.86/1.73  #Sup     : 387
% 3.86/1.73  #Fact    : 0
% 3.86/1.73  #Define  : 0
% 3.86/1.73  #Split   : 2
% 3.86/1.73  #Chain   : 0
% 3.86/1.73  #Close   : 0
% 3.86/1.73  
% 3.86/1.73  Ordering : KBO
% 3.86/1.73  
% 3.86/1.73  Simplification rules
% 3.86/1.73  ----------------------
% 3.86/1.73  #Subsume      : 22
% 3.86/1.73  #Demod        : 246
% 3.86/1.73  #Tautology    : 193
% 3.86/1.73  #SimpNegUnit  : 1
% 3.86/1.73  #BackRed      : 6
% 3.86/1.73  
% 3.86/1.73  #Partial instantiations: 0
% 3.86/1.73  #Strategies tried      : 1
% 3.86/1.73  
% 3.86/1.73  Timing (in seconds)
% 3.86/1.73  ----------------------
% 3.86/1.74  Preprocessing        : 0.38
% 3.86/1.74  Parsing              : 0.21
% 3.86/1.74  CNF conversion       : 0.02
% 3.86/1.74  Main loop            : 0.53
% 3.86/1.74  Inferencing          : 0.20
% 3.86/1.74  Reduction            : 0.17
% 3.86/1.74  Demodulation         : 0.13
% 3.86/1.74  BG Simplification    : 0.03
% 3.86/1.74  Subsumption          : 0.08
% 3.86/1.74  Abstraction          : 0.03
% 3.86/1.74  MUC search           : 0.00
% 3.86/1.74  Cooper               : 0.00
% 3.86/1.74  Total                : 0.95
% 3.86/1.74  Index Insertion      : 0.00
% 3.86/1.74  Index Deletion       : 0.00
% 3.86/1.74  Index Matching       : 0.00
% 3.86/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
