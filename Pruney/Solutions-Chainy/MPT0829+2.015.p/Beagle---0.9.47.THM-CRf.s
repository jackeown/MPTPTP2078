%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:23 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 265 expanded)
%              Number of leaves         :   42 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 431 expanded)
%              Number of equality atoms :   37 ( 176 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_91,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1444,plain,(
    ! [A_201,B_202,C_203] :
      ( k2_relset_1(A_201,B_202,C_203) = k2_relat_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1453,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1444])).

tff(c_54,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_916,plain,(
    ! [C_136,A_137,B_138,D_139] :
      ( r1_tarski(C_136,k1_relset_1(A_137,B_138,D_139))
      | ~ r1_tarski(k6_relat_1(C_136),D_139)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_969,plain,(
    ! [A_140,B_141] :
      ( r1_tarski('#skF_2',k1_relset_1(A_140,B_141,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(resolution,[status(thm)],[c_56,c_916])).

tff(c_975,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_969])).

tff(c_980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_975])).

tff(c_981,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1454,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_981])).

tff(c_1699,plain,(
    ! [C_212,A_213,B_214,D_215] :
      ( r1_tarski(C_212,k2_relset_1(A_213,B_214,D_215))
      | ~ r1_tarski(k6_relat_1(C_212),D_215)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1737,plain,(
    ! [A_216,B_217] :
      ( r1_tarski('#skF_2',k2_relset_1(A_216,B_217,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(resolution,[status(thm)],[c_56,c_1699])).

tff(c_1743,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_1737])).

tff(c_1746,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_1743])).

tff(c_30,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1152,plain,(
    ! [A_171,B_172] :
      ( k5_relat_1(k6_relat_1(A_171),B_172) = k7_relat_1(B_172,A_171)
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [B_33,A_32] : k5_relat_1(k6_relat_1(B_33),k6_relat_1(A_32)) = k6_relat_1(k3_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1159,plain,(
    ! [A_32,A_171] :
      ( k7_relat_1(k6_relat_1(A_32),A_171) = k6_relat_1(k3_xboole_0(A_32,A_171))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1152,c_42])).

tff(c_1168,plain,(
    ! [A_32,A_171] : k7_relat_1(k6_relat_1(A_32),A_171) = k6_relat_1(k3_xboole_0(A_32,A_171)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1159])).

tff(c_1280,plain,(
    ! [B_190,A_191] :
      ( k7_relat_1(B_190,A_191) = B_190
      | ~ r1_tarski(k1_relat_1(B_190),A_191)
      | ~ v1_relat_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1283,plain,(
    ! [A_26,A_191] :
      ( k7_relat_1(k6_relat_1(A_26),A_191) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_191)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1280])).

tff(c_1297,plain,(
    ! [A_195,A_196] :
      ( k6_relat_1(k3_xboole_0(A_195,A_196)) = k6_relat_1(A_195)
      | ~ r1_tarski(A_195,A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1168,c_1283])).

tff(c_1330,plain,(
    ! [A_195,A_196] :
      ( k3_xboole_0(A_195,A_196) = k1_relat_1(k6_relat_1(A_195))
      | ~ r1_tarski(A_195,A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1297,c_30])).

tff(c_1353,plain,(
    ! [A_195,A_196] :
      ( k3_xboole_0(A_195,A_196) = A_195
      | ~ r1_tarski(A_195,A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1330])).

tff(c_1757,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1746,c_1353])).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1016,plain,(
    ! [B_148,A_149] :
      ( v1_relat_1(B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_149))
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1022,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_1016])).

tff(c_1026,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1022])).

tff(c_1050,plain,(
    ! [C_152,B_153,A_154] :
      ( v5_relat_1(C_152,B_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1059,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1050])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_992,plain,(
    ! [A_144,B_145] : k1_setfam_1(k2_tarski(A_144,B_145)) = k3_xboole_0(A_144,B_145) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1027,plain,(
    ! [B_150,A_151] : k1_setfam_1(k2_tarski(B_150,A_151)) = k3_xboole_0(A_151,B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_992])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1033,plain,(
    ! [B_150,A_151] : k3_xboole_0(B_150,A_151) = k3_xboole_0(A_151,B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_8])).

tff(c_1346,plain,(
    ! [A_151,B_150] :
      ( k6_relat_1(k3_xboole_0(A_151,B_150)) = k6_relat_1(B_150)
      | ~ r1_tarski(B_150,A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_1297])).

tff(c_1762,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_1346])).

tff(c_1811,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1762])).

tff(c_1824,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1811])).

tff(c_1828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_1059,c_1824])).

tff(c_1830,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1762])).

tff(c_1471,plain,(
    ! [A_204,B_205] :
      ( k6_relat_1(k3_xboole_0(A_204,B_205)) = k6_relat_1(B_205)
      | ~ r1_tarski(B_205,A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_1297])).

tff(c_1507,plain,(
    ! [A_204,B_205] :
      ( k3_xboole_0(A_204,B_205) = k1_relat_1(k6_relat_1(B_205))
      | ~ r1_tarski(B_205,A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1471,c_30])).

tff(c_1545,plain,(
    ! [A_204,B_205] :
      ( k3_xboole_0(A_204,B_205) = B_205
      | ~ r1_tarski(B_205,A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1507])).

tff(c_1833,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1830,c_1545])).

tff(c_1844,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_1833])).

tff(c_1846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1454,c_1844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.66  
% 3.81/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.67  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.81/1.67  
% 3.81/1.67  %Foreground sorts:
% 3.81/1.67  
% 3.81/1.67  
% 3.81/1.67  %Background operators:
% 3.81/1.67  
% 3.81/1.67  
% 3.81/1.67  %Foreground operators:
% 3.81/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.81/1.67  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.81/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.81/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.81/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.81/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.81/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.81/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.81/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.81/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.81/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.81/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.81/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.81/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.81/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.81/1.67  
% 3.81/1.68  tff(f_118, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 3.81/1.68  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.81/1.68  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 3.81/1.68  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.81/1.68  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.81/1.68  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.81/1.68  tff(f_91, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.81/1.68  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.81/1.68  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.81/1.68  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.81/1.68  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.81/1.68  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.81/1.68  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.81/1.68  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.81/1.68  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.81/1.68  tff(c_1444, plain, (![A_201, B_202, C_203]: (k2_relset_1(A_201, B_202, C_203)=k2_relat_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.81/1.68  tff(c_1453, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1444])).
% 3.81/1.68  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.81/1.68  tff(c_114, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.81/1.68  tff(c_56, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.81/1.68  tff(c_916, plain, (![C_136, A_137, B_138, D_139]: (r1_tarski(C_136, k1_relset_1(A_137, B_138, D_139)) | ~r1_tarski(k6_relat_1(C_136), D_139) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.81/1.68  tff(c_969, plain, (![A_140, B_141]: (r1_tarski('#skF_2', k1_relset_1(A_140, B_141, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(resolution, [status(thm)], [c_56, c_916])).
% 3.81/1.68  tff(c_975, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_969])).
% 3.81/1.68  tff(c_980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_975])).
% 3.81/1.68  tff(c_981, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 3.81/1.68  tff(c_1454, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_981])).
% 3.81/1.68  tff(c_1699, plain, (![C_212, A_213, B_214, D_215]: (r1_tarski(C_212, k2_relset_1(A_213, B_214, D_215)) | ~r1_tarski(k6_relat_1(C_212), D_215) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.81/1.68  tff(c_1737, plain, (![A_216, B_217]: (r1_tarski('#skF_2', k2_relset_1(A_216, B_217, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(resolution, [status(thm)], [c_56, c_1699])).
% 3.81/1.68  tff(c_1743, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_1737])).
% 3.81/1.68  tff(c_1746, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_1743])).
% 3.81/1.68  tff(c_30, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.81/1.68  tff(c_38, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.81/1.68  tff(c_1152, plain, (![A_171, B_172]: (k5_relat_1(k6_relat_1(A_171), B_172)=k7_relat_1(B_172, A_171) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.68  tff(c_42, plain, (![B_33, A_32]: (k5_relat_1(k6_relat_1(B_33), k6_relat_1(A_32))=k6_relat_1(k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.81/1.68  tff(c_1159, plain, (![A_32, A_171]: (k7_relat_1(k6_relat_1(A_32), A_171)=k6_relat_1(k3_xboole_0(A_32, A_171)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_1152, c_42])).
% 3.81/1.68  tff(c_1168, plain, (![A_32, A_171]: (k7_relat_1(k6_relat_1(A_32), A_171)=k6_relat_1(k3_xboole_0(A_32, A_171)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1159])).
% 3.81/1.68  tff(c_1280, plain, (![B_190, A_191]: (k7_relat_1(B_190, A_191)=B_190 | ~r1_tarski(k1_relat_1(B_190), A_191) | ~v1_relat_1(B_190))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.81/1.68  tff(c_1283, plain, (![A_26, A_191]: (k7_relat_1(k6_relat_1(A_26), A_191)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_191) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1280])).
% 3.81/1.68  tff(c_1297, plain, (![A_195, A_196]: (k6_relat_1(k3_xboole_0(A_195, A_196))=k6_relat_1(A_195) | ~r1_tarski(A_195, A_196))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1168, c_1283])).
% 3.81/1.68  tff(c_1330, plain, (![A_195, A_196]: (k3_xboole_0(A_195, A_196)=k1_relat_1(k6_relat_1(A_195)) | ~r1_tarski(A_195, A_196))), inference(superposition, [status(thm), theory('equality')], [c_1297, c_30])).
% 3.81/1.68  tff(c_1353, plain, (![A_195, A_196]: (k3_xboole_0(A_195, A_196)=A_195 | ~r1_tarski(A_195, A_196))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1330])).
% 3.81/1.68  tff(c_1757, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_1746, c_1353])).
% 3.81/1.68  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.81/1.68  tff(c_1016, plain, (![B_148, A_149]: (v1_relat_1(B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_149)) | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.81/1.68  tff(c_1022, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_1016])).
% 3.81/1.68  tff(c_1026, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1022])).
% 3.81/1.68  tff(c_1050, plain, (![C_152, B_153, A_154]: (v5_relat_1(C_152, B_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.81/1.68  tff(c_1059, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1050])).
% 3.81/1.68  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.81/1.68  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.68  tff(c_992, plain, (![A_144, B_145]: (k1_setfam_1(k2_tarski(A_144, B_145))=k3_xboole_0(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.68  tff(c_1027, plain, (![B_150, A_151]: (k1_setfam_1(k2_tarski(B_150, A_151))=k3_xboole_0(A_151, B_150))), inference(superposition, [status(thm), theory('equality')], [c_2, c_992])).
% 3.81/1.68  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.68  tff(c_1033, plain, (![B_150, A_151]: (k3_xboole_0(B_150, A_151)=k3_xboole_0(A_151, B_150))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_8])).
% 3.81/1.68  tff(c_1346, plain, (![A_151, B_150]: (k6_relat_1(k3_xboole_0(A_151, B_150))=k6_relat_1(B_150) | ~r1_tarski(B_150, A_151))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_1297])).
% 3.81/1.68  tff(c_1762, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1757, c_1346])).
% 3.81/1.68  tff(c_1811, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1762])).
% 3.81/1.68  tff(c_1824, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1811])).
% 3.81/1.68  tff(c_1828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1026, c_1059, c_1824])).
% 3.81/1.68  tff(c_1830, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1762])).
% 3.81/1.68  tff(c_1471, plain, (![A_204, B_205]: (k6_relat_1(k3_xboole_0(A_204, B_205))=k6_relat_1(B_205) | ~r1_tarski(B_205, A_204))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_1297])).
% 3.81/1.68  tff(c_1507, plain, (![A_204, B_205]: (k3_xboole_0(A_204, B_205)=k1_relat_1(k6_relat_1(B_205)) | ~r1_tarski(B_205, A_204))), inference(superposition, [status(thm), theory('equality')], [c_1471, c_30])).
% 3.81/1.68  tff(c_1545, plain, (![A_204, B_205]: (k3_xboole_0(A_204, B_205)=B_205 | ~r1_tarski(B_205, A_204))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1507])).
% 3.81/1.68  tff(c_1833, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1830, c_1545])).
% 3.81/1.68  tff(c_1844, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_1833])).
% 3.81/1.68  tff(c_1846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1454, c_1844])).
% 3.81/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.68  
% 3.81/1.68  Inference rules
% 3.81/1.68  ----------------------
% 3.81/1.68  #Ref     : 0
% 3.81/1.68  #Sup     : 434
% 3.81/1.68  #Fact    : 0
% 3.81/1.68  #Define  : 0
% 3.81/1.68  #Split   : 13
% 3.81/1.68  #Chain   : 0
% 3.81/1.68  #Close   : 0
% 3.81/1.68  
% 3.81/1.68  Ordering : KBO
% 3.81/1.68  
% 3.81/1.68  Simplification rules
% 3.81/1.68  ----------------------
% 3.81/1.68  #Subsume      : 15
% 3.81/1.68  #Demod        : 171
% 3.81/1.68  #Tautology    : 211
% 3.81/1.68  #SimpNegUnit  : 2
% 3.81/1.68  #BackRed      : 1
% 3.81/1.68  
% 3.81/1.68  #Partial instantiations: 0
% 3.81/1.68  #Strategies tried      : 1
% 3.81/1.68  
% 3.81/1.68  Timing (in seconds)
% 3.81/1.68  ----------------------
% 3.81/1.69  Preprocessing        : 0.31
% 3.81/1.69  Parsing              : 0.16
% 3.81/1.69  CNF conversion       : 0.02
% 3.81/1.69  Main loop            : 0.53
% 3.81/1.69  Inferencing          : 0.19
% 3.81/1.69  Reduction            : 0.19
% 3.81/1.69  Demodulation         : 0.14
% 3.81/1.69  BG Simplification    : 0.03
% 3.81/1.69  Subsumption          : 0.08
% 3.81/1.69  Abstraction          : 0.03
% 3.81/1.69  MUC search           : 0.00
% 3.81/1.69  Cooper               : 0.00
% 3.81/1.69  Total                : 0.88
% 3.81/1.69  Index Insertion      : 0.00
% 3.81/1.69  Index Deletion       : 0.00
% 3.81/1.69  Index Matching       : 0.00
% 3.81/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
