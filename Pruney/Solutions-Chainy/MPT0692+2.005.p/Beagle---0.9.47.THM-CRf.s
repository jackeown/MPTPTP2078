%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:50 EST 2020

% Result     : Theorem 11.84s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :  133 (1534 expanded)
%              Number of leaves         :   36 ( 532 expanded)
%              Depth                    :   30
%              Number of atoms          :  211 (2535 expanded)
%              Number of equality atoms :  108 (1322 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(A,k2_relat_1(B))
         => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k9_relat_1(B_37,k10_relat_1(B_37,A_36)),A_36)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_124,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_188,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [B_59] : k4_xboole_0(B_59,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_156,plain,(
    ! [B_62] : r1_tarski(k1_xboole_0,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_14])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [B_62] : k4_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_12])).

tff(c_224,plain,(
    ! [B_66] : k3_xboole_0(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_229,plain,(
    ! [B_66] : k3_xboole_0(B_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_281,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1032,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(A_100,B_101) = A_100
      | ~ r1_tarski(A_100,k4_xboole_0(A_100,B_101)) ) ),
    inference(resolution,[status(thm)],[c_14,c_281])).

tff(c_1079,plain,(
    ! [A_5,B_101] :
      ( k4_xboole_0(A_5,B_101) = A_5
      | k4_xboole_0(A_5,k4_xboole_0(A_5,B_101)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1032])).

tff(c_1108,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = A_104
      | k3_xboole_0(A_104,B_105) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1079])).

tff(c_140,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_220,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_188])).

tff(c_1166,plain,(
    ! [A_104] :
      ( k3_xboole_0(A_104,A_104) = A_104
      | k3_xboole_0(A_104,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1108,c_220])).

tff(c_1260,plain,(
    ! [A_104] : k3_xboole_0(A_104,A_104) = A_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_1166])).

tff(c_1294,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_220])).

tff(c_146,plain,(
    ! [B_59] : r1_tarski(k1_xboole_0,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_14])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_393,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_xboole_0(A_75,C_76)
      | ~ r1_xboole_0(B_77,C_76)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1740,plain,(
    ! [A_126,B_127,A_128] :
      ( r1_xboole_0(A_126,B_127)
      | ~ r1_tarski(A_126,A_128)
      | k4_xboole_0(A_128,B_127) != A_128 ) ),
    inference(resolution,[status(thm)],[c_22,c_393])).

tff(c_1813,plain,(
    ! [B_131,B_132] :
      ( r1_xboole_0(k1_xboole_0,B_131)
      | k4_xboole_0(B_132,B_131) != B_132 ) ),
    inference(resolution,[status(thm)],[c_146,c_1740])).

tff(c_1840,plain,(
    ! [B_133] : r1_xboole_0(k1_xboole_0,B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_1813])).

tff(c_18,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1866,plain,(
    ! [A_136,B_137] :
      ( r1_xboole_0(A_136,B_137)
      | ~ r1_tarski(A_136,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1840,c_18])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1940,plain,(
    ! [A_142,B_143] :
      ( k4_xboole_0(A_142,B_143) = A_142
      | ~ r1_tarski(A_142,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1866,c_20])).

tff(c_1955,plain,(
    ! [A_5,B_143] :
      ( k4_xboole_0(A_5,B_143) = A_5
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1940])).

tff(c_1977,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,B_145) = A_144
      | k1_xboole_0 != A_144 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1955])).

tff(c_2025,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,A_144) = k3_xboole_0(A_144,B_145)
      | k1_xboole_0 != A_144 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_16])).

tff(c_2092,plain,(
    ! [A_146,B_147] :
      ( k3_xboole_0(A_146,B_147) = k1_xboole_0
      | k1_xboole_0 != A_146 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2025])).

tff(c_2352,plain,(
    ! [A_153,B_154] :
      ( k3_xboole_0(A_153,B_154) = k1_xboole_0
      | k1_xboole_0 != B_154 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2092])).

tff(c_191,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,k4_xboole_0(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_16])).

tff(c_2368,plain,(
    ! [A_153,B_154] :
      ( k3_xboole_0(A_153,k4_xboole_0(A_153,B_154)) = k4_xboole_0(A_153,k1_xboole_0)
      | k1_xboole_0 != B_154 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_191])).

tff(c_3636,plain,(
    ! [A_183,B_184] :
      ( k3_xboole_0(A_183,k4_xboole_0(A_183,B_184)) = A_183
      | k1_xboole_0 != B_184 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_2368])).

tff(c_305,plain,(
    ! [A_70,B_71] : r1_tarski(k3_xboole_0(A_70,B_71),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_14])).

tff(c_319,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_305])).

tff(c_3805,plain,(
    ! [A_185,B_186] :
      ( r1_tarski(A_185,k4_xboole_0(A_185,B_186))
      | k1_xboole_0 != B_186 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3636,c_319])).

tff(c_296,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_281])).

tff(c_3813,plain,(
    ! [A_185,B_186] :
      ( k4_xboole_0(A_185,B_186) = A_185
      | k4_xboole_0(k4_xboole_0(A_185,B_186),A_185) != k1_xboole_0
      | k1_xboole_0 != B_186 ) ),
    inference(resolution,[status(thm)],[c_3805,c_296])).

tff(c_3895,plain,(
    ! [A_185] : k4_xboole_0(A_185,k1_xboole_0) = A_185 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3813])).

tff(c_3897,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(A_187,B_188) = A_187
      | k1_xboole_0 != B_188 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_3813])).

tff(c_873,plain,(
    ! [B_94,A_95] :
      ( k10_relat_1(B_94,A_95) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_94),A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_878,plain,(
    ! [B_94,B_15] :
      ( k10_relat_1(B_94,B_15) = k1_xboole_0
      | ~ v1_relat_1(B_94)
      | k4_xboole_0(k2_relat_1(B_94),B_15) != k2_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_22,c_873])).

tff(c_5683,plain,(
    ! [B_237,B_238] :
      ( k10_relat_1(B_237,B_238) = k1_xboole_0
      | ~ v1_relat_1(B_237)
      | k1_xboole_0 != B_238 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_878])).

tff(c_5689,plain,(
    ! [B_239] :
      ( k10_relat_1('#skF_2',B_239) = k1_xboole_0
      | k1_xboole_0 != B_239 ) ),
    inference(resolution,[status(thm)],[c_52,c_5683])).

tff(c_30,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [C_35,A_33,B_34] :
      ( k6_subset_1(k10_relat_1(C_35,A_33),k10_relat_1(C_35,B_34)) = k10_relat_1(C_35,k6_subset_1(A_33,B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_53,plain,(
    ! [C_35,A_33,B_34] :
      ( k4_xboole_0(k10_relat_1(C_35,A_33),k10_relat_1(C_35,B_34)) = k10_relat_1(C_35,k4_xboole_0(A_33,B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_40])).

tff(c_5747,plain,(
    ! [A_33,B_239] :
      ( k4_xboole_0(k10_relat_1('#skF_2',A_33),k1_xboole_0) = k10_relat_1('#skF_2',k4_xboole_0(A_33,B_239))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_239 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5689,c_53])).

tff(c_11762,plain,(
    ! [A_314,B_315] :
      ( k10_relat_1('#skF_2',k4_xboole_0(A_314,B_315)) = k10_relat_1('#skF_2',A_314)
      | k1_xboole_0 != B_315 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3895,c_5747])).

tff(c_34,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k10_relat_1(B_30,A_29),k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_11819,plain,(
    ! [A_314,B_315] :
      ( r1_tarski(k10_relat_1('#skF_2',A_314),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2')
      | k1_xboole_0 != B_315 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11762,c_34])).

tff(c_11925,plain,(
    ! [A_314,B_315] :
      ( r1_tarski(k10_relat_1('#skF_2',A_314),k1_relat_1('#skF_2'))
      | k1_xboole_0 != B_315 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11819])).

tff(c_11946,plain,(
    ! [B_315] : k1_xboole_0 != B_315 ),
    inference(splitLeft,[status(thm)],[c_11925])).

tff(c_2208,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_16])).

tff(c_488,plain,(
    ! [A_81,B_82] : k4_xboole_0(k3_xboole_0(A_81,B_82),A_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_305,c_12])).

tff(c_516,plain,(
    ! [A_1,B_2] : k4_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_488])).

tff(c_324,plain,(
    ! [A_70,B_71] : k4_xboole_0(k3_xboole_0(A_70,B_71),A_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_305,c_12])).

tff(c_5856,plain,(
    ! [A_241,B_242] :
      ( k3_xboole_0(A_241,B_242) = A_241
      | k4_xboole_0(A_241,B_242) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_16])).

tff(c_6687,plain,(
    ! [A_254,B_255] : k3_xboole_0(k3_xboole_0(A_254,B_255),A_254) = k3_xboole_0(A_254,B_255) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_5856])).

tff(c_7370,plain,(
    ! [A_264,B_265] : k3_xboole_0(k3_xboole_0(A_264,B_265),B_265) = k3_xboole_0(B_265,A_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6687])).

tff(c_7441,plain,(
    ! [A_264,B_265] : k3_xboole_0(k3_xboole_0(A_264,B_265),k4_xboole_0(k3_xboole_0(A_264,B_265),B_265)) = k4_xboole_0(k3_xboole_0(A_264,B_265),k3_xboole_0(B_265,A_264)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7370,c_191])).

tff(c_7571,plain,(
    ! [A_264,B_265] : k4_xboole_0(k3_xboole_0(A_264,B_265),k3_xboole_0(B_265,A_264)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2208,c_2,c_516,c_7441])).

tff(c_11978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11946,c_7571])).

tff(c_11979,plain,(
    ! [A_314] : r1_tarski(k10_relat_1('#skF_2',A_314),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_11925])).

tff(c_1850,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(A_134,k10_relat_1(B_135,k9_relat_1(B_135,A_134)))
      | ~ r1_tarski(A_134,k1_relat_1(B_135))
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4661,plain,(
    ! [A_213,B_214] :
      ( k4_xboole_0(A_213,k10_relat_1(B_214,k9_relat_1(B_214,A_213))) = k1_xboole_0
      | ~ r1_tarski(A_213,k1_relat_1(B_214))
      | ~ v1_relat_1(B_214) ) ),
    inference(resolution,[status(thm)],[c_1850,c_12])).

tff(c_35670,plain,(
    ! [B_603,A_604] :
      ( k10_relat_1(B_603,k4_xboole_0(A_604,k9_relat_1(B_603,k10_relat_1(B_603,A_604)))) = k1_xboole_0
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603)
      | ~ r1_tarski(k10_relat_1(B_603,A_604),k1_relat_1(B_603))
      | ~ v1_relat_1(B_603) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4661,c_53])).

tff(c_1096,plain,(
    ! [B_102,A_103] :
      ( r1_xboole_0(k2_relat_1(B_102),A_103)
      | k10_relat_1(B_102,A_103) != k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2879,plain,(
    ! [B_166,A_167] :
      ( k4_xboole_0(k2_relat_1(B_166),A_167) = k2_relat_1(B_166)
      | k10_relat_1(B_166,A_167) != k1_xboole_0
      | ~ v1_relat_1(B_166) ) ),
    inference(resolution,[status(thm)],[c_1096,c_20])).

tff(c_48,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1766,plain,(
    ! [B_127] :
      ( r1_xboole_0('#skF_1',B_127)
      | k4_xboole_0(k2_relat_1('#skF_2'),B_127) != k2_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1740])).

tff(c_2900,plain,(
    ! [A_167] :
      ( r1_xboole_0('#skF_1',A_167)
      | k10_relat_1('#skF_2',A_167) != k1_xboole_0
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2879,c_1766])).

tff(c_2988,plain,(
    ! [A_168] :
      ( r1_xboole_0('#skF_1',A_168)
      | k10_relat_1('#skF_2',A_168) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2900])).

tff(c_3090,plain,(
    ! [A_172] :
      ( k4_xboole_0('#skF_1',A_172) = '#skF_1'
      | k10_relat_1('#skF_2',A_172) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2988,c_20])).

tff(c_3166,plain,(
    ! [B_10] :
      ( k3_xboole_0('#skF_1',B_10) = '#skF_1'
      | k10_relat_1('#skF_2',k4_xboole_0('#skF_1',B_10)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3090])).

tff(c_35735,plain,
    ( k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ r1_tarski(k10_relat_1('#skF_2','#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35670,c_3166])).

tff(c_36020,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11979,c_50,c_35735])).

tff(c_1062,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = A_9
      | ~ r1_tarski(A_9,k3_xboole_0(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1032])).

tff(c_1519,plain,(
    ! [A_112,B_113] :
      ( k3_xboole_0(A_112,B_113) = A_112
      | ~ r1_tarski(A_112,k3_xboole_0(A_112,B_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1062])).

tff(c_1545,plain,(
    ! [B_2,A_1] :
      ( k3_xboole_0(B_2,A_1) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1519])).

tff(c_36291,plain,
    ( k3_xboole_0(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') = k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36020,c_1545])).

tff(c_36370,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36020,c_2,c_36291])).

tff(c_36371,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36370])).

tff(c_36397,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_36371])).

tff(c_36409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.84/5.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.57  
% 11.95/5.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.57  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.95/5.57  
% 11.95/5.57  %Foreground sorts:
% 11.95/5.57  
% 11.95/5.57  
% 11.95/5.57  %Background operators:
% 11.95/5.57  
% 11.95/5.57  
% 11.95/5.57  %Foreground operators:
% 11.95/5.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.95/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.95/5.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.95/5.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.95/5.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.95/5.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.95/5.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.95/5.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.95/5.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.95/5.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.95/5.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.95/5.57  tff('#skF_2', type, '#skF_2': $i).
% 11.95/5.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.95/5.57  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.95/5.57  tff('#skF_1', type, '#skF_1': $i).
% 11.95/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.95/5.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.95/5.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.95/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.95/5.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.95/5.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.95/5.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.95/5.57  
% 11.95/5.60  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 11.95/5.60  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 11.95/5.60  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.95/5.60  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.95/5.60  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.95/5.60  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.95/5.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.95/5.60  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.95/5.60  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.95/5.60  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 11.95/5.60  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.95/5.60  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 11.95/5.60  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 11.95/5.60  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 11.95/5.60  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.95/5.60  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.95/5.60  tff(c_42, plain, (![B_37, A_36]: (r1_tarski(k9_relat_1(B_37, k10_relat_1(B_37, A_36)), A_36) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.95/5.60  tff(c_46, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.95/5.60  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.95/5.60  tff(c_124, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.95/5.60  tff(c_138, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_124])).
% 11.95/5.60  tff(c_188, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.95/5.60  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.95/5.60  tff(c_141, plain, (![B_59]: (k4_xboole_0(B_59, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_124])).
% 11.95/5.60  tff(c_156, plain, (![B_62]: (r1_tarski(k1_xboole_0, B_62))), inference(superposition, [status(thm), theory('equality')], [c_141, c_14])).
% 11.95/5.60  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.95/5.60  tff(c_160, plain, (![B_62]: (k4_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_156, c_12])).
% 11.95/5.60  tff(c_224, plain, (![B_66]: (k3_xboole_0(k1_xboole_0, B_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_160])).
% 11.95/5.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.95/5.60  tff(c_229, plain, (![B_66]: (k3_xboole_0(B_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_2])).
% 11.95/5.60  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.95/5.60  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.95/5.60  tff(c_281, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.95/5.60  tff(c_1032, plain, (![A_100, B_101]: (k4_xboole_0(A_100, B_101)=A_100 | ~r1_tarski(A_100, k4_xboole_0(A_100, B_101)))), inference(resolution, [status(thm)], [c_14, c_281])).
% 11.95/5.60  tff(c_1079, plain, (![A_5, B_101]: (k4_xboole_0(A_5, B_101)=A_5 | k4_xboole_0(A_5, k4_xboole_0(A_5, B_101))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1032])).
% 11.95/5.60  tff(c_1108, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=A_104 | k3_xboole_0(A_104, B_105)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1079])).
% 11.95/5.60  tff(c_140, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_124])).
% 11.95/5.60  tff(c_220, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_140, c_188])).
% 11.95/5.60  tff(c_1166, plain, (![A_104]: (k3_xboole_0(A_104, A_104)=A_104 | k3_xboole_0(A_104, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1108, c_220])).
% 11.95/5.60  tff(c_1260, plain, (![A_104]: (k3_xboole_0(A_104, A_104)=A_104)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_1166])).
% 11.95/5.60  tff(c_1294, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_220])).
% 11.95/5.60  tff(c_146, plain, (![B_59]: (r1_tarski(k1_xboole_0, B_59))), inference(superposition, [status(thm), theory('equality')], [c_141, c_14])).
% 11.95/5.60  tff(c_22, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.95/5.60  tff(c_393, plain, (![A_75, C_76, B_77]: (r1_xboole_0(A_75, C_76) | ~r1_xboole_0(B_77, C_76) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.95/5.60  tff(c_1740, plain, (![A_126, B_127, A_128]: (r1_xboole_0(A_126, B_127) | ~r1_tarski(A_126, A_128) | k4_xboole_0(A_128, B_127)!=A_128)), inference(resolution, [status(thm)], [c_22, c_393])).
% 11.95/5.60  tff(c_1813, plain, (![B_131, B_132]: (r1_xboole_0(k1_xboole_0, B_131) | k4_xboole_0(B_132, B_131)!=B_132)), inference(resolution, [status(thm)], [c_146, c_1740])).
% 11.95/5.60  tff(c_1840, plain, (![B_133]: (r1_xboole_0(k1_xboole_0, B_133))), inference(superposition, [status(thm), theory('equality')], [c_160, c_1813])).
% 11.95/5.60  tff(c_18, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_xboole_0(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.95/5.60  tff(c_1866, plain, (![A_136, B_137]: (r1_xboole_0(A_136, B_137) | ~r1_tarski(A_136, k1_xboole_0))), inference(resolution, [status(thm)], [c_1840, c_18])).
% 11.95/5.60  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.95/5.60  tff(c_1940, plain, (![A_142, B_143]: (k4_xboole_0(A_142, B_143)=A_142 | ~r1_tarski(A_142, k1_xboole_0))), inference(resolution, [status(thm)], [c_1866, c_20])).
% 11.95/5.60  tff(c_1955, plain, (![A_5, B_143]: (k4_xboole_0(A_5, B_143)=A_5 | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1940])).
% 11.95/5.60  tff(c_1977, plain, (![A_144, B_145]: (k4_xboole_0(A_144, B_145)=A_144 | k1_xboole_0!=A_144)), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1955])).
% 11.95/5.60  tff(c_2025, plain, (![A_144, B_145]: (k4_xboole_0(A_144, A_144)=k3_xboole_0(A_144, B_145) | k1_xboole_0!=A_144)), inference(superposition, [status(thm), theory('equality')], [c_1977, c_16])).
% 11.95/5.60  tff(c_2092, plain, (![A_146, B_147]: (k3_xboole_0(A_146, B_147)=k1_xboole_0 | k1_xboole_0!=A_146)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2025])).
% 11.95/5.60  tff(c_2352, plain, (![A_153, B_154]: (k3_xboole_0(A_153, B_154)=k1_xboole_0 | k1_xboole_0!=B_154)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2092])).
% 11.95/5.60  tff(c_191, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k3_xboole_0(A_64, k4_xboole_0(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_16])).
% 11.95/5.60  tff(c_2368, plain, (![A_153, B_154]: (k3_xboole_0(A_153, k4_xboole_0(A_153, B_154))=k4_xboole_0(A_153, k1_xboole_0) | k1_xboole_0!=B_154)), inference(superposition, [status(thm), theory('equality')], [c_2352, c_191])).
% 11.95/5.60  tff(c_3636, plain, (![A_183, B_184]: (k3_xboole_0(A_183, k4_xboole_0(A_183, B_184))=A_183 | k1_xboole_0!=B_184)), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_2368])).
% 11.95/5.60  tff(c_305, plain, (![A_70, B_71]: (r1_tarski(k3_xboole_0(A_70, B_71), A_70))), inference(superposition, [status(thm), theory('equality')], [c_188, c_14])).
% 11.95/5.60  tff(c_319, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_305])).
% 11.95/5.60  tff(c_3805, plain, (![A_185, B_186]: (r1_tarski(A_185, k4_xboole_0(A_185, B_186)) | k1_xboole_0!=B_186)), inference(superposition, [status(thm), theory('equality')], [c_3636, c_319])).
% 11.95/5.60  tff(c_296, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_281])).
% 11.95/5.60  tff(c_3813, plain, (![A_185, B_186]: (k4_xboole_0(A_185, B_186)=A_185 | k4_xboole_0(k4_xboole_0(A_185, B_186), A_185)!=k1_xboole_0 | k1_xboole_0!=B_186)), inference(resolution, [status(thm)], [c_3805, c_296])).
% 11.95/5.60  tff(c_3895, plain, (![A_185]: (k4_xboole_0(A_185, k1_xboole_0)=A_185)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_3813])).
% 11.95/5.60  tff(c_3897, plain, (![A_187, B_188]: (k4_xboole_0(A_187, B_188)=A_187 | k1_xboole_0!=B_188)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_3813])).
% 11.95/5.60  tff(c_873, plain, (![B_94, A_95]: (k10_relat_1(B_94, A_95)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_94), A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.95/5.60  tff(c_878, plain, (![B_94, B_15]: (k10_relat_1(B_94, B_15)=k1_xboole_0 | ~v1_relat_1(B_94) | k4_xboole_0(k2_relat_1(B_94), B_15)!=k2_relat_1(B_94))), inference(resolution, [status(thm)], [c_22, c_873])).
% 11.95/5.60  tff(c_5683, plain, (![B_237, B_238]: (k10_relat_1(B_237, B_238)=k1_xboole_0 | ~v1_relat_1(B_237) | k1_xboole_0!=B_238)), inference(superposition, [status(thm), theory('equality')], [c_3897, c_878])).
% 11.95/5.60  tff(c_5689, plain, (![B_239]: (k10_relat_1('#skF_2', B_239)=k1_xboole_0 | k1_xboole_0!=B_239)), inference(resolution, [status(thm)], [c_52, c_5683])).
% 11.95/5.60  tff(c_30, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.95/5.60  tff(c_40, plain, (![C_35, A_33, B_34]: (k6_subset_1(k10_relat_1(C_35, A_33), k10_relat_1(C_35, B_34))=k10_relat_1(C_35, k6_subset_1(A_33, B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.95/5.60  tff(c_53, plain, (![C_35, A_33, B_34]: (k4_xboole_0(k10_relat_1(C_35, A_33), k10_relat_1(C_35, B_34))=k10_relat_1(C_35, k4_xboole_0(A_33, B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_40])).
% 11.95/5.60  tff(c_5747, plain, (![A_33, B_239]: (k4_xboole_0(k10_relat_1('#skF_2', A_33), k1_xboole_0)=k10_relat_1('#skF_2', k4_xboole_0(A_33, B_239)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_239)), inference(superposition, [status(thm), theory('equality')], [c_5689, c_53])).
% 11.95/5.60  tff(c_11762, plain, (![A_314, B_315]: (k10_relat_1('#skF_2', k4_xboole_0(A_314, B_315))=k10_relat_1('#skF_2', A_314) | k1_xboole_0!=B_315)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_3895, c_5747])).
% 11.95/5.60  tff(c_34, plain, (![B_30, A_29]: (r1_tarski(k10_relat_1(B_30, A_29), k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.95/5.60  tff(c_11819, plain, (![A_314, B_315]: (r1_tarski(k10_relat_1('#skF_2', A_314), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | k1_xboole_0!=B_315)), inference(superposition, [status(thm), theory('equality')], [c_11762, c_34])).
% 11.95/5.60  tff(c_11925, plain, (![A_314, B_315]: (r1_tarski(k10_relat_1('#skF_2', A_314), k1_relat_1('#skF_2')) | k1_xboole_0!=B_315)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11819])).
% 11.95/5.60  tff(c_11946, plain, (![B_315]: (k1_xboole_0!=B_315)), inference(splitLeft, [status(thm)], [c_11925])).
% 11.95/5.60  tff(c_2208, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1977, c_16])).
% 11.95/5.60  tff(c_488, plain, (![A_81, B_82]: (k4_xboole_0(k3_xboole_0(A_81, B_82), A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_305, c_12])).
% 11.95/5.60  tff(c_516, plain, (![A_1, B_2]: (k4_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_488])).
% 11.95/5.60  tff(c_324, plain, (![A_70, B_71]: (k4_xboole_0(k3_xboole_0(A_70, B_71), A_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_305, c_12])).
% 11.95/5.60  tff(c_5856, plain, (![A_241, B_242]: (k3_xboole_0(A_241, B_242)=A_241 | k4_xboole_0(A_241, B_242)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3897, c_16])).
% 11.95/5.60  tff(c_6687, plain, (![A_254, B_255]: (k3_xboole_0(k3_xboole_0(A_254, B_255), A_254)=k3_xboole_0(A_254, B_255))), inference(superposition, [status(thm), theory('equality')], [c_324, c_5856])).
% 11.95/5.60  tff(c_7370, plain, (![A_264, B_265]: (k3_xboole_0(k3_xboole_0(A_264, B_265), B_265)=k3_xboole_0(B_265, A_264))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6687])).
% 11.95/5.60  tff(c_7441, plain, (![A_264, B_265]: (k3_xboole_0(k3_xboole_0(A_264, B_265), k4_xboole_0(k3_xboole_0(A_264, B_265), B_265))=k4_xboole_0(k3_xboole_0(A_264, B_265), k3_xboole_0(B_265, A_264)))), inference(superposition, [status(thm), theory('equality')], [c_7370, c_191])).
% 11.95/5.60  tff(c_7571, plain, (![A_264, B_265]: (k4_xboole_0(k3_xboole_0(A_264, B_265), k3_xboole_0(B_265, A_264))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2208, c_2, c_516, c_7441])).
% 11.95/5.60  tff(c_11978, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11946, c_7571])).
% 11.95/5.60  tff(c_11979, plain, (![A_314]: (r1_tarski(k10_relat_1('#skF_2', A_314), k1_relat_1('#skF_2')))), inference(splitRight, [status(thm)], [c_11925])).
% 11.95/5.60  tff(c_1850, plain, (![A_134, B_135]: (r1_tarski(A_134, k10_relat_1(B_135, k9_relat_1(B_135, A_134))) | ~r1_tarski(A_134, k1_relat_1(B_135)) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.95/5.60  tff(c_4661, plain, (![A_213, B_214]: (k4_xboole_0(A_213, k10_relat_1(B_214, k9_relat_1(B_214, A_213)))=k1_xboole_0 | ~r1_tarski(A_213, k1_relat_1(B_214)) | ~v1_relat_1(B_214))), inference(resolution, [status(thm)], [c_1850, c_12])).
% 11.95/5.60  tff(c_35670, plain, (![B_603, A_604]: (k10_relat_1(B_603, k4_xboole_0(A_604, k9_relat_1(B_603, k10_relat_1(B_603, A_604))))=k1_xboole_0 | ~v1_funct_1(B_603) | ~v1_relat_1(B_603) | ~r1_tarski(k10_relat_1(B_603, A_604), k1_relat_1(B_603)) | ~v1_relat_1(B_603))), inference(superposition, [status(thm), theory('equality')], [c_4661, c_53])).
% 11.95/5.60  tff(c_1096, plain, (![B_102, A_103]: (r1_xboole_0(k2_relat_1(B_102), A_103) | k10_relat_1(B_102, A_103)!=k1_xboole_0 | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.95/5.60  tff(c_2879, plain, (![B_166, A_167]: (k4_xboole_0(k2_relat_1(B_166), A_167)=k2_relat_1(B_166) | k10_relat_1(B_166, A_167)!=k1_xboole_0 | ~v1_relat_1(B_166))), inference(resolution, [status(thm)], [c_1096, c_20])).
% 11.95/5.60  tff(c_48, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.95/5.60  tff(c_1766, plain, (![B_127]: (r1_xboole_0('#skF_1', B_127) | k4_xboole_0(k2_relat_1('#skF_2'), B_127)!=k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1740])).
% 11.95/5.60  tff(c_2900, plain, (![A_167]: (r1_xboole_0('#skF_1', A_167) | k10_relat_1('#skF_2', A_167)!=k1_xboole_0 | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2879, c_1766])).
% 11.95/5.60  tff(c_2988, plain, (![A_168]: (r1_xboole_0('#skF_1', A_168) | k10_relat_1('#skF_2', A_168)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2900])).
% 11.95/5.60  tff(c_3090, plain, (![A_172]: (k4_xboole_0('#skF_1', A_172)='#skF_1' | k10_relat_1('#skF_2', A_172)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2988, c_20])).
% 11.95/5.60  tff(c_3166, plain, (![B_10]: (k3_xboole_0('#skF_1', B_10)='#skF_1' | k10_relat_1('#skF_2', k4_xboole_0('#skF_1', B_10))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_3090])).
% 11.95/5.60  tff(c_35735, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~v1_funct_1('#skF_2') | ~r1_tarski(k10_relat_1('#skF_2', '#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35670, c_3166])).
% 11.95/5.60  tff(c_36020, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11979, c_50, c_35735])).
% 11.95/5.60  tff(c_1062, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=A_9 | ~r1_tarski(A_9, k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1032])).
% 11.95/5.60  tff(c_1519, plain, (![A_112, B_113]: (k3_xboole_0(A_112, B_113)=A_112 | ~r1_tarski(A_112, k3_xboole_0(A_112, B_113)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1062])).
% 11.95/5.60  tff(c_1545, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=B_2 | ~r1_tarski(B_2, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1519])).
% 11.95/5.60  tff(c_36291, plain, (k3_xboole_0(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36020, c_1545])).
% 11.95/5.60  tff(c_36370, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36020, c_2, c_36291])).
% 11.95/5.60  tff(c_36371, plain, (~r1_tarski(k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_36370])).
% 11.95/5.60  tff(c_36397, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_36371])).
% 11.95/5.60  tff(c_36409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36397])).
% 11.95/5.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.60  
% 11.95/5.60  Inference rules
% 11.95/5.60  ----------------------
% 11.95/5.60  #Ref     : 2
% 11.95/5.60  #Sup     : 9110
% 11.95/5.60  #Fact    : 0
% 11.95/5.60  #Define  : 0
% 11.95/5.60  #Split   : 15
% 11.95/5.60  #Chain   : 0
% 11.95/5.60  #Close   : 0
% 11.95/5.60  
% 11.95/5.60  Ordering : KBO
% 11.95/5.60  
% 11.95/5.60  Simplification rules
% 11.95/5.60  ----------------------
% 11.95/5.60  #Subsume      : 4022
% 11.95/5.60  #Demod        : 6191
% 11.95/5.60  #Tautology    : 3060
% 11.95/5.60  #SimpNegUnit  : 355
% 11.95/5.60  #BackRed      : 34
% 11.95/5.60  
% 11.95/5.60  #Partial instantiations: 0
% 11.95/5.60  #Strategies tried      : 1
% 11.95/5.60  
% 11.95/5.60  Timing (in seconds)
% 11.95/5.60  ----------------------
% 11.95/5.60  Preprocessing        : 0.32
% 11.95/5.60  Parsing              : 0.17
% 11.95/5.60  CNF conversion       : 0.02
% 11.95/5.60  Main loop            : 4.39
% 11.95/5.60  Inferencing          : 0.81
% 11.95/5.60  Reduction            : 2.17
% 11.95/5.60  Demodulation         : 1.77
% 11.95/5.60  BG Simplification    : 0.09
% 11.95/5.60  Subsumption          : 1.12
% 11.95/5.60  Abstraction          : 0.15
% 11.95/5.60  MUC search           : 0.00
% 11.95/5.60  Cooper               : 0.00
% 11.95/5.60  Total                : 4.76
% 11.95/5.60  Index Insertion      : 0.00
% 11.95/5.60  Index Deletion       : 0.00
% 11.95/5.60  Index Matching       : 0.00
% 11.95/5.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
