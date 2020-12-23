%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:04 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 164 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 260 expanded)
%              Number of equality atoms :   58 ( 101 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_163,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_171,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_28])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [A_28,B_29] : r1_tarski(k4_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_118,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_140,plain,(
    ! [A_37] : r1_tarski(k1_xboole_0,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_12])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1514,plain,(
    ! [A_103,B_104] :
      ( k2_xboole_0(A_103,B_104) = B_104
      | k4_xboole_0(A_103,B_104) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_243])).

tff(c_1571,plain,(
    ! [A_105] :
      ( k2_xboole_0(A_105,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1514])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1622,plain,(
    ! [A_105,C_7] :
      ( r1_tarski(A_105,C_7)
      | ~ r1_tarski(k1_xboole_0,C_7)
      | k1_xboole_0 != A_105 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1571,c_8])).

tff(c_1716,plain,(
    ! [A_107,C_108] :
      ( r1_tarski(A_107,C_108)
      | k1_xboole_0 != A_107 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1622])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1746,plain,(
    ! [A_109,C_110] :
      ( k4_xboole_0(A_109,C_110) = k1_xboole_0
      | k1_xboole_0 != A_109 ) ),
    inference(resolution,[status(thm)],[c_1716,c_6])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1796,plain,(
    ! [A_109,B_14] :
      ( k3_xboole_0(A_109,B_14) = k1_xboole_0
      | k1_xboole_0 != A_109 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1746,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_300,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_325,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_300])).

tff(c_4994,plain,(
    ! [A_208,B_209] : k3_xboole_0(k4_xboole_0(A_208,B_209),A_208) = k4_xboole_0(A_208,B_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_325])).

tff(c_5177,plain,(
    ! [A_1,B_209] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_209)) = k4_xboole_0(A_1,B_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4994])).

tff(c_2434,plain,(
    ! [A_125,B_126] : k4_xboole_0(A_125,k3_xboole_0(A_125,B_126)) = k3_xboole_0(A_125,k4_xboole_0(A_125,B_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_300])).

tff(c_2504,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2434])).

tff(c_6270,plain,(
    ! [B_227,A_228] : k4_xboole_0(B_227,k3_xboole_0(A_228,B_227)) = k4_xboole_0(B_227,A_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5177,c_2504])).

tff(c_6400,plain,(
    ! [B_14,A_109] :
      ( k4_xboole_0(B_14,k1_xboole_0) = k4_xboole_0(B_14,A_109)
      | k1_xboole_0 != A_109 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_6270])).

tff(c_6454,plain,(
    ! [B_14] : k4_xboole_0(B_14,k1_xboole_0) = B_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_6400])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_132,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_20,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [C_23,A_21,B_22] :
      ( k6_subset_1(k10_relat_1(C_23,A_21),k10_relat_1(C_23,B_22)) = k10_relat_1(C_23,k6_subset_1(A_21,B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_954,plain,(
    ! [C_78,A_79,B_80] :
      ( k4_xboole_0(k10_relat_1(C_78,A_79),k10_relat_1(C_78,B_80)) = k10_relat_1(C_78,k4_xboole_0(A_79,B_80))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_24])).

tff(c_980,plain,(
    ! [C_78,A_79] :
      ( k10_relat_1(C_78,k4_xboole_0(A_79,A_79)) = k1_xboole_0
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_954])).

tff(c_6736,plain,(
    ! [C_232] :
      ( k10_relat_1(C_232,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_232)
      | ~ v1_relat_1(C_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_980])).

tff(c_6739,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_6736])).

tff(c_6742,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6739])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_267,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_243])).

tff(c_266,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_12,c_243])).

tff(c_417,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(k2_xboole_0(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_497,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(A_57,B_58)) ),
    inference(resolution,[status(thm)],[c_70,c_417])).

tff(c_1076,plain,(
    ! [A_84,B_85,B_86] : r1_tarski(A_84,k2_xboole_0(k2_xboole_0(A_84,B_85),B_86)) ),
    inference(resolution,[status(thm)],[c_497,c_8])).

tff(c_1339,plain,(
    ! [A_96,B_97,B_98] : r1_tarski(k4_xboole_0(A_96,B_97),k2_xboole_0(A_96,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_1076])).

tff(c_1381,plain,(
    ! [B_97] : r1_tarski(k4_xboole_0('#skF_1',B_97),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_1339])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [C_20,A_18,B_19] :
      ( k6_subset_1(k9_relat_1(C_20,A_18),k9_relat_1(C_20,B_19)) = k9_relat_1(C_20,k6_subset_1(A_18,B_19))
      | ~ v2_funct_1(C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1157,plain,(
    ! [C_88,A_89,B_90] :
      ( k4_xboole_0(k9_relat_1(C_88,A_89),k9_relat_1(C_88,B_90)) = k9_relat_1(C_88,k4_xboole_0(A_89,B_90))
      | ~ v2_funct_1(C_88)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_34,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_131,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_118])).

tff(c_1172,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_131])).

tff(c_1192,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1172])).

tff(c_667,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,k10_relat_1(B_67,k9_relat_1(B_67,A_66)))
      | ~ r1_tarski(A_66,k1_relat_1(B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3054,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(A_154,k10_relat_1(B_155,k9_relat_1(B_155,A_154))) = k1_xboole_0
      | ~ r1_tarski(A_154,k1_relat_1(B_155))
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_667,c_6])).

tff(c_3118,plain,
    ( k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_3054])).

tff(c_3140,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1381,c_3118])).

tff(c_10517,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6454,c_6742,c_3140])).

tff(c_10518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_10517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.22/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.66  
% 7.22/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.66  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.22/2.66  
% 7.22/2.66  %Foreground sorts:
% 7.22/2.66  
% 7.22/2.66  
% 7.22/2.66  %Background operators:
% 7.22/2.66  
% 7.22/2.66  
% 7.22/2.66  %Foreground operators:
% 7.22/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.22/2.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.22/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.22/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.22/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.22/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.22/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.22/2.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.22/2.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.22/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.22/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.22/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.22/2.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.22/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.22/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.22/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.22/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.22/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.22/2.66  
% 7.22/2.68  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.22/2.68  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 7.22/2.68  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.22/2.68  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.22/2.68  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.22/2.68  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.22/2.68  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.22/2.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.22/2.68  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.22/2.68  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 7.22/2.68  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 7.22/2.68  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 7.22/2.68  tff(c_163, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.68  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.68  tff(c_171, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_28])).
% 7.22/2.68  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.22/2.68  tff(c_67, plain, (![A_28, B_29]: (r1_tarski(k4_xboole_0(A_28, B_29), A_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.22/2.68  tff(c_70, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 7.22/2.68  tff(c_118, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.68  tff(c_135, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_118])).
% 7.22/2.68  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.22/2.68  tff(c_140, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37))), inference(superposition, [status(thm), theory('equality')], [c_135, c_12])).
% 7.22/2.68  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.68  tff(c_243, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.22/2.68  tff(c_1514, plain, (![A_103, B_104]: (k2_xboole_0(A_103, B_104)=B_104 | k4_xboole_0(A_103, B_104)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_243])).
% 7.22/2.68  tff(c_1571, plain, (![A_105]: (k2_xboole_0(A_105, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_105)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1514])).
% 7.22/2.68  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.22/2.68  tff(c_1622, plain, (![A_105, C_7]: (r1_tarski(A_105, C_7) | ~r1_tarski(k1_xboole_0, C_7) | k1_xboole_0!=A_105)), inference(superposition, [status(thm), theory('equality')], [c_1571, c_8])).
% 7.22/2.68  tff(c_1716, plain, (![A_107, C_108]: (r1_tarski(A_107, C_108) | k1_xboole_0!=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1622])).
% 7.22/2.68  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.68  tff(c_1746, plain, (![A_109, C_110]: (k4_xboole_0(A_109, C_110)=k1_xboole_0 | k1_xboole_0!=A_109)), inference(resolution, [status(thm)], [c_1716, c_6])).
% 7.22/2.68  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.68  tff(c_1796, plain, (![A_109, B_14]: (k3_xboole_0(A_109, B_14)=k1_xboole_0 | k1_xboole_0!=A_109)), inference(superposition, [status(thm), theory('equality')], [c_1746, c_16])).
% 7.22/2.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.22/2.68  tff(c_133, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_118])).
% 7.22/2.68  tff(c_300, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.68  tff(c_325, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_133, c_300])).
% 7.22/2.68  tff(c_4994, plain, (![A_208, B_209]: (k3_xboole_0(k4_xboole_0(A_208, B_209), A_208)=k4_xboole_0(A_208, B_209))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_325])).
% 7.22/2.68  tff(c_5177, plain, (![A_1, B_209]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_209))=k4_xboole_0(A_1, B_209))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4994])).
% 7.22/2.68  tff(c_2434, plain, (![A_125, B_126]: (k4_xboole_0(A_125, k3_xboole_0(A_125, B_126))=k3_xboole_0(A_125, k4_xboole_0(A_125, B_126)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_300])).
% 7.22/2.68  tff(c_2504, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2434])).
% 7.22/2.68  tff(c_6270, plain, (![B_227, A_228]: (k4_xboole_0(B_227, k3_xboole_0(A_228, B_227))=k4_xboole_0(B_227, A_228))), inference(demodulation, [status(thm), theory('equality')], [c_5177, c_2504])).
% 7.22/2.68  tff(c_6400, plain, (![B_14, A_109]: (k4_xboole_0(B_14, k1_xboole_0)=k4_xboole_0(B_14, A_109) | k1_xboole_0!=A_109)), inference(superposition, [status(thm), theory('equality')], [c_1796, c_6270])).
% 7.22/2.68  tff(c_6454, plain, (![B_14]: (k4_xboole_0(B_14, k1_xboole_0)=B_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_6400])).
% 7.22/2.68  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.68  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.68  tff(c_132, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_118])).
% 7.22/2.68  tff(c_20, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.22/2.68  tff(c_24, plain, (![C_23, A_21, B_22]: (k6_subset_1(k10_relat_1(C_23, A_21), k10_relat_1(C_23, B_22))=k10_relat_1(C_23, k6_subset_1(A_21, B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.22/2.68  tff(c_954, plain, (![C_78, A_79, B_80]: (k4_xboole_0(k10_relat_1(C_78, A_79), k10_relat_1(C_78, B_80))=k10_relat_1(C_78, k4_xboole_0(A_79, B_80)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_24])).
% 7.22/2.68  tff(c_980, plain, (![C_78, A_79]: (k10_relat_1(C_78, k4_xboole_0(A_79, A_79))=k1_xboole_0 | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(superposition, [status(thm), theory('equality')], [c_132, c_954])).
% 7.22/2.68  tff(c_6736, plain, (![C_232]: (k10_relat_1(C_232, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_232) | ~v1_relat_1(C_232))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_980])).
% 7.22/2.68  tff(c_6739, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_6736])).
% 7.22/2.68  tff(c_6742, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6739])).
% 7.22/2.68  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.68  tff(c_267, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_243])).
% 7.22/2.68  tff(c_266, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_12, c_243])).
% 7.22/2.68  tff(c_417, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.22/2.68  tff(c_497, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_70, c_417])).
% 7.22/2.68  tff(c_1076, plain, (![A_84, B_85, B_86]: (r1_tarski(A_84, k2_xboole_0(k2_xboole_0(A_84, B_85), B_86)))), inference(resolution, [status(thm)], [c_497, c_8])).
% 7.22/2.68  tff(c_1339, plain, (![A_96, B_97, B_98]: (r1_tarski(k4_xboole_0(A_96, B_97), k2_xboole_0(A_96, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_266, c_1076])).
% 7.22/2.68  tff(c_1381, plain, (![B_97]: (r1_tarski(k4_xboole_0('#skF_1', B_97), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_267, c_1339])).
% 7.22/2.68  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.68  tff(c_22, plain, (![C_20, A_18, B_19]: (k6_subset_1(k9_relat_1(C_20, A_18), k9_relat_1(C_20, B_19))=k9_relat_1(C_20, k6_subset_1(A_18, B_19)) | ~v2_funct_1(C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.22/2.68  tff(c_1157, plain, (![C_88, A_89, B_90]: (k4_xboole_0(k9_relat_1(C_88, A_89), k9_relat_1(C_88, B_90))=k9_relat_1(C_88, k4_xboole_0(A_89, B_90)) | ~v2_funct_1(C_88) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 7.22/2.68  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.22/2.68  tff(c_131, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_118])).
% 7.22/2.68  tff(c_1172, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1157, c_131])).
% 7.22/2.68  tff(c_1192, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1172])).
% 7.22/2.68  tff(c_667, plain, (![A_66, B_67]: (r1_tarski(A_66, k10_relat_1(B_67, k9_relat_1(B_67, A_66))) | ~r1_tarski(A_66, k1_relat_1(B_67)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.22/2.68  tff(c_3054, plain, (![A_154, B_155]: (k4_xboole_0(A_154, k10_relat_1(B_155, k9_relat_1(B_155, A_154)))=k1_xboole_0 | ~r1_tarski(A_154, k1_relat_1(B_155)) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_667, c_6])).
% 7.22/2.68  tff(c_3118, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1192, c_3054])).
% 7.22/2.68  tff(c_3140, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1381, c_3118])).
% 7.22/2.68  tff(c_10517, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6454, c_6742, c_3140])).
% 7.22/2.68  tff(c_10518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_10517])).
% 7.22/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.68  
% 7.22/2.68  Inference rules
% 7.22/2.68  ----------------------
% 7.22/2.68  #Ref     : 1
% 7.22/2.68  #Sup     : 2671
% 7.22/2.68  #Fact    : 0
% 7.22/2.68  #Define  : 0
% 7.22/2.68  #Split   : 3
% 7.22/2.68  #Chain   : 0
% 7.22/2.68  #Close   : 0
% 7.22/2.68  
% 7.22/2.68  Ordering : KBO
% 7.22/2.68  
% 7.22/2.68  Simplification rules
% 7.22/2.68  ----------------------
% 7.22/2.68  #Subsume      : 526
% 7.22/2.68  #Demod        : 1858
% 7.22/2.68  #Tautology    : 1491
% 7.22/2.68  #SimpNegUnit  : 18
% 7.22/2.68  #BackRed      : 1
% 7.22/2.68  
% 7.22/2.68  #Partial instantiations: 0
% 7.22/2.68  #Strategies tried      : 1
% 7.22/2.68  
% 7.22/2.68  Timing (in seconds)
% 7.22/2.68  ----------------------
% 7.22/2.68  Preprocessing        : 0.32
% 7.22/2.68  Parsing              : 0.18
% 7.22/2.68  CNF conversion       : 0.02
% 7.22/2.68  Main loop            : 1.52
% 7.22/2.68  Inferencing          : 0.40
% 7.22/2.68  Reduction            : 0.72
% 7.22/2.68  Demodulation         : 0.60
% 7.22/2.68  BG Simplification    : 0.04
% 7.22/2.68  Subsumption          : 0.27
% 7.22/2.68  Abstraction          : 0.07
% 7.22/2.68  MUC search           : 0.00
% 7.22/2.68  Cooper               : 0.00
% 7.22/2.68  Total                : 1.88
% 7.22/2.68  Index Insertion      : 0.00
% 7.22/2.68  Index Deletion       : 0.00
% 7.22/2.68  Index Matching       : 0.00
% 7.22/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
