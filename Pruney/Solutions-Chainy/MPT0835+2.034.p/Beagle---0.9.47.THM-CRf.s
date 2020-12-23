%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:00 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 198 expanded)
%              Number of leaves         :   40 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 341 expanded)
%              Number of equality atoms :   68 ( 132 expanded)
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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_46,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_76,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_954,plain,(
    ! [B_140,A_141] :
      ( k5_relat_1(B_140,k6_relat_1(A_141)) = B_140
      | ~ r1_tarski(k2_relat_1(B_140),A_141)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_971,plain,(
    ! [B_140] :
      ( k5_relat_1(B_140,k6_relat_1(k2_relat_1(B_140))) = B_140
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_6,c_954])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1092,plain,(
    ! [A_151,B_152] :
      ( k10_relat_1(A_151,k1_relat_1(B_152)) = k1_relat_1(k5_relat_1(A_151,B_152))
      | ~ v1_relat_1(B_152)
      | ~ v1_relat_1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1101,plain,(
    ! [A_151,A_16] :
      ( k1_relat_1(k5_relat_1(A_151,k6_relat_1(A_16))) = k10_relat_1(A_151,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1092])).

tff(c_1106,plain,(
    ! [A_153,A_154] :
      ( k1_relat_1(k5_relat_1(A_153,k6_relat_1(A_154))) = k10_relat_1(A_153,A_154)
      | ~ v1_relat_1(A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1101])).

tff(c_1136,plain,(
    ! [B_140] :
      ( k10_relat_1(B_140,k2_relat_1(B_140)) = k1_relat_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_1106])).

tff(c_1325,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k7_relset_1(A_167,B_168,C_169,D_170) = k9_relat_1(C_169,D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1328,plain,(
    ! [D_170] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_170) = k9_relat_1('#skF_3',D_170) ),
    inference(resolution,[status(thm)],[c_46,c_1325])).

tff(c_1029,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relset_1(A_146,B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1033,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1029])).

tff(c_1426,plain,(
    ! [A_176,B_177,C_178] :
      ( k7_relset_1(A_176,B_177,C_178,A_176) = k2_relset_1(A_176,B_177,C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1428,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1426])).

tff(c_1430,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1033,c_1428])).

tff(c_1143,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k8_relset_1(A_155,B_156,C_157,D_158) = k10_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1146,plain,(
    ! [D_158] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_158) = k10_relat_1('#skF_3',D_158) ),
    inference(resolution,[status(thm)],[c_46,c_1143])).

tff(c_161,plain,(
    ! [B_66,A_67] :
      ( k7_relat_1(B_66,A_67) = B_66
      | ~ r1_tarski(k1_relat_1(B_66),A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_172,plain,(
    ! [B_68] :
      ( k7_relat_1(B_68,k1_relat_1(B_68)) = B_68
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_178,plain,(
    ! [B_68] :
      ( k9_relat_1(B_68,k1_relat_1(B_68)) = k2_relat_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_18])).

tff(c_94,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_94])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_203,plain,(
    ! [B_70,A_71] :
      ( k5_relat_1(B_70,k6_relat_1(A_71)) = B_70
      | ~ r1_tarski(k2_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_217,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_409,plain,(
    ! [A_86,B_87] :
      ( k10_relat_1(A_86,k1_relat_1(B_87)) = k1_relat_1(k5_relat_1(A_86,B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_418,plain,(
    ! [A_86,A_16] :
      ( k1_relat_1(k5_relat_1(A_86,k6_relat_1(A_16))) = k10_relat_1(A_86,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_409])).

tff(c_423,plain,(
    ! [A_88,A_89] :
      ( k1_relat_1(k5_relat_1(A_88,k6_relat_1(A_89))) = k10_relat_1(A_88,A_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_418])).

tff(c_696,plain,(
    ! [B_110,A_111] :
      ( k10_relat_1(B_110,A_111) = k1_relat_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v5_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_423])).

tff(c_708,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_696])).

tff(c_718,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_708])).

tff(c_682,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k8_relset_1(A_105,B_106,C_107,D_108) = k10_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_685,plain,(
    ! [D_108] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_108) = k10_relat_1('#skF_3',D_108) ),
    inference(resolution,[status(thm)],[c_46,c_682])).

tff(c_649,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_652,plain,(
    ! [D_101] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_101) = k9_relat_1('#skF_3',D_101) ),
    inference(resolution,[status(thm)],[c_46,c_649])).

tff(c_256,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_260,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_256])).

tff(c_44,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_83,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_261,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_83])).

tff(c_653,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_261])).

tff(c_686,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_653])).

tff(c_719,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_686])).

tff(c_726,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_719])).

tff(c_730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_726])).

tff(c_731,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1169,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_731])).

tff(c_1329,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1169])).

tff(c_1431,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_1329])).

tff(c_1438,plain,
    ( k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1136,c_1431])).

tff(c_1440,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_1438])).

tff(c_786,plain,(
    ! [C_122,B_123,A_124] :
      ( v5_relat_1(C_122,B_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_790,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_786])).

tff(c_968,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_954])).

tff(c_1369,plain,(
    ! [B_174,A_175] :
      ( k10_relat_1(B_174,A_175) = k1_relat_1(B_174)
      | ~ v1_relat_1(B_174)
      | ~ v5_relat_1(B_174,A_175)
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_1106])).

tff(c_1372,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_790,c_1369])).

tff(c_1384,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1372])).

tff(c_1441,plain,(
    ! [A_179,B_180,C_181] :
      ( k8_relset_1(A_179,B_180,C_181,B_180) = k1_relset_1(A_179,B_180,C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1443,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1441])).

tff(c_1445,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_1146,c_1443])).

tff(c_1447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1440,c_1445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.56  
% 3.25/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.56  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.56  
% 3.25/1.56  %Foreground sorts:
% 3.25/1.56  
% 3.25/1.56  
% 3.25/1.56  %Background operators:
% 3.25/1.56  
% 3.25/1.56  
% 3.25/1.56  %Foreground operators:
% 3.25/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.25/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.25/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.25/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.25/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.25/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.25/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.25/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.25/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.25/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.56  
% 3.25/1.58  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.25/1.58  tff(f_106, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.25/1.58  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.25/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/1.58  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.25/1.58  tff(f_46, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.25/1.58  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.25/1.58  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.25/1.58  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.25/1.58  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.25/1.58  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.25/1.58  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.25/1.58  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.25/1.58  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.25/1.58  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.25/1.58  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.25/1.58  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.58  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.58  tff(c_76, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.25/1.58  tff(c_79, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_76])).
% 3.25/1.58  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 3.25/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.58  tff(c_954, plain, (![B_140, A_141]: (k5_relat_1(B_140, k6_relat_1(A_141))=B_140 | ~r1_tarski(k2_relat_1(B_140), A_141) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.58  tff(c_971, plain, (![B_140]: (k5_relat_1(B_140, k6_relat_1(k2_relat_1(B_140)))=B_140 | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_6, c_954])).
% 3.25/1.58  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.25/1.58  tff(c_22, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.25/1.58  tff(c_1092, plain, (![A_151, B_152]: (k10_relat_1(A_151, k1_relat_1(B_152))=k1_relat_1(k5_relat_1(A_151, B_152)) | ~v1_relat_1(B_152) | ~v1_relat_1(A_151))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.58  tff(c_1101, plain, (![A_151, A_16]: (k1_relat_1(k5_relat_1(A_151, k6_relat_1(A_16)))=k10_relat_1(A_151, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1092])).
% 3.25/1.58  tff(c_1106, plain, (![A_153, A_154]: (k1_relat_1(k5_relat_1(A_153, k6_relat_1(A_154)))=k10_relat_1(A_153, A_154) | ~v1_relat_1(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1101])).
% 3.25/1.58  tff(c_1136, plain, (![B_140]: (k10_relat_1(B_140, k2_relat_1(B_140))=k1_relat_1(B_140) | ~v1_relat_1(B_140) | ~v1_relat_1(B_140))), inference(superposition, [status(thm), theory('equality')], [c_971, c_1106])).
% 3.25/1.58  tff(c_1325, plain, (![A_167, B_168, C_169, D_170]: (k7_relset_1(A_167, B_168, C_169, D_170)=k9_relat_1(C_169, D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.25/1.58  tff(c_1328, plain, (![D_170]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_170)=k9_relat_1('#skF_3', D_170))), inference(resolution, [status(thm)], [c_46, c_1325])).
% 3.25/1.58  tff(c_1029, plain, (![A_146, B_147, C_148]: (k2_relset_1(A_146, B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.25/1.58  tff(c_1033, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1029])).
% 3.25/1.58  tff(c_1426, plain, (![A_176, B_177, C_178]: (k7_relset_1(A_176, B_177, C_178, A_176)=k2_relset_1(A_176, B_177, C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.25/1.58  tff(c_1428, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1426])).
% 3.25/1.58  tff(c_1430, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1033, c_1428])).
% 3.25/1.58  tff(c_1143, plain, (![A_155, B_156, C_157, D_158]: (k8_relset_1(A_155, B_156, C_157, D_158)=k10_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.58  tff(c_1146, plain, (![D_158]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_158)=k10_relat_1('#skF_3', D_158))), inference(resolution, [status(thm)], [c_46, c_1143])).
% 3.25/1.58  tff(c_161, plain, (![B_66, A_67]: (k7_relat_1(B_66, A_67)=B_66 | ~r1_tarski(k1_relat_1(B_66), A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.25/1.58  tff(c_172, plain, (![B_68]: (k7_relat_1(B_68, k1_relat_1(B_68))=B_68 | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_6, c_161])).
% 3.25/1.58  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.25/1.58  tff(c_178, plain, (![B_68]: (k9_relat_1(B_68, k1_relat_1(B_68))=k2_relat_1(B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_172, c_18])).
% 3.25/1.58  tff(c_94, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.25/1.58  tff(c_98, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_94])).
% 3.25/1.58  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.25/1.58  tff(c_203, plain, (![B_70, A_71]: (k5_relat_1(B_70, k6_relat_1(A_71))=B_70 | ~r1_tarski(k2_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.58  tff(c_217, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_203])).
% 3.25/1.58  tff(c_409, plain, (![A_86, B_87]: (k10_relat_1(A_86, k1_relat_1(B_87))=k1_relat_1(k5_relat_1(A_86, B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.58  tff(c_418, plain, (![A_86, A_16]: (k1_relat_1(k5_relat_1(A_86, k6_relat_1(A_16)))=k10_relat_1(A_86, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_22, c_409])).
% 3.25/1.58  tff(c_423, plain, (![A_88, A_89]: (k1_relat_1(k5_relat_1(A_88, k6_relat_1(A_89)))=k10_relat_1(A_88, A_89) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_418])).
% 3.25/1.58  tff(c_696, plain, (![B_110, A_111]: (k10_relat_1(B_110, A_111)=k1_relat_1(B_110) | ~v1_relat_1(B_110) | ~v5_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_217, c_423])).
% 3.25/1.58  tff(c_708, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_696])).
% 3.25/1.58  tff(c_718, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_708])).
% 3.25/1.58  tff(c_682, plain, (![A_105, B_106, C_107, D_108]: (k8_relset_1(A_105, B_106, C_107, D_108)=k10_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.58  tff(c_685, plain, (![D_108]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_108)=k10_relat_1('#skF_3', D_108))), inference(resolution, [status(thm)], [c_46, c_682])).
% 3.25/1.58  tff(c_649, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.25/1.58  tff(c_652, plain, (![D_101]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_101)=k9_relat_1('#skF_3', D_101))), inference(resolution, [status(thm)], [c_46, c_649])).
% 3.25/1.58  tff(c_256, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.25/1.58  tff(c_260, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_256])).
% 3.25/1.58  tff(c_44, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.58  tff(c_83, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.25/1.58  tff(c_261, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_83])).
% 3.25/1.58  tff(c_653, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_652, c_261])).
% 3.25/1.58  tff(c_686, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_685, c_653])).
% 3.25/1.58  tff(c_719, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_686])).
% 3.25/1.58  tff(c_726, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_719])).
% 3.25/1.58  tff(c_730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_726])).
% 3.25/1.58  tff(c_731, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.25/1.58  tff(c_1169, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_731])).
% 3.25/1.58  tff(c_1329, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1169])).
% 3.25/1.58  tff(c_1431, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1430, c_1329])).
% 3.25/1.58  tff(c_1438, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1136, c_1431])).
% 3.25/1.58  tff(c_1440, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_1438])).
% 3.25/1.58  tff(c_786, plain, (![C_122, B_123, A_124]: (v5_relat_1(C_122, B_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.25/1.58  tff(c_790, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_786])).
% 3.25/1.58  tff(c_968, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_954])).
% 3.25/1.58  tff(c_1369, plain, (![B_174, A_175]: (k10_relat_1(B_174, A_175)=k1_relat_1(B_174) | ~v1_relat_1(B_174) | ~v5_relat_1(B_174, A_175) | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_968, c_1106])).
% 3.25/1.58  tff(c_1372, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_790, c_1369])).
% 3.25/1.58  tff(c_1384, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1372])).
% 3.25/1.58  tff(c_1441, plain, (![A_179, B_180, C_181]: (k8_relset_1(A_179, B_180, C_181, B_180)=k1_relset_1(A_179, B_180, C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.25/1.58  tff(c_1443, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1441])).
% 3.25/1.58  tff(c_1445, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_1146, c_1443])).
% 3.25/1.58  tff(c_1447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1440, c_1445])).
% 3.25/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.58  
% 3.25/1.58  Inference rules
% 3.25/1.58  ----------------------
% 3.25/1.58  #Ref     : 0
% 3.25/1.58  #Sup     : 294
% 3.25/1.58  #Fact    : 0
% 3.25/1.58  #Define  : 0
% 3.25/1.58  #Split   : 1
% 3.25/1.58  #Chain   : 0
% 3.25/1.58  #Close   : 0
% 3.25/1.58  
% 3.25/1.58  Ordering : KBO
% 3.25/1.58  
% 3.25/1.58  Simplification rules
% 3.25/1.58  ----------------------
% 3.25/1.58  #Subsume      : 8
% 3.25/1.58  #Demod        : 259
% 3.25/1.58  #Tautology    : 183
% 3.25/1.58  #SimpNegUnit  : 1
% 3.25/1.58  #BackRed      : 11
% 3.25/1.58  
% 3.25/1.58  #Partial instantiations: 0
% 3.25/1.58  #Strategies tried      : 1
% 3.25/1.58  
% 3.25/1.58  Timing (in seconds)
% 3.25/1.58  ----------------------
% 3.25/1.58  Preprocessing        : 0.34
% 3.25/1.58  Parsing              : 0.19
% 3.25/1.58  CNF conversion       : 0.02
% 3.25/1.58  Main loop            : 0.42
% 3.25/1.58  Inferencing          : 0.17
% 3.25/1.58  Reduction            : 0.13
% 3.25/1.58  Demodulation         : 0.10
% 3.25/1.58  BG Simplification    : 0.02
% 3.25/1.58  Subsumption          : 0.06
% 3.25/1.58  Abstraction          : 0.03
% 3.25/1.58  MUC search           : 0.00
% 3.25/1.58  Cooper               : 0.00
% 3.25/1.58  Total                : 0.80
% 3.25/1.58  Index Insertion      : 0.00
% 3.25/1.58  Index Deletion       : 0.00
% 3.25/1.58  Index Matching       : 0.00
% 3.25/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
