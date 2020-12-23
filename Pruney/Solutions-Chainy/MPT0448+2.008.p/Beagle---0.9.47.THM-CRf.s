%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:36 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   69 (  93 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :   57 (  84 expanded)
%              Number of equality atoms :   46 (  69 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_8,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_enumset1(A_27,A_27,B_28,C_29,D_30,E_31) = k3_enumset1(A_27,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k5_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43,G_44) = k5_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [B_115,H_119,A_121,G_120,C_116,D_117,E_118,F_114] : k2_xboole_0(k5_enumset1(A_121,B_115,C_116,D_117,E_118,F_114,G_120),k1_tarski(H_119)) = k6_enumset1(A_121,B_115,C_116,D_117,E_118,F_114,G_120,H_119) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_266,plain,(
    ! [B_33,C_34,H_119,E_36,F_37,A_32,D_35] : k6_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37,H_119) = k2_xboole_0(k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37),k1_tarski(H_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_257])).

tff(c_270,plain,(
    ! [C_126,F_124,A_127,H_125,E_122,D_128,B_123] : k2_xboole_0(k4_enumset1(A_127,B_123,C_126,D_128,E_122,F_124),k1_tarski(H_125)) = k5_enumset1(A_127,B_123,C_126,D_128,E_122,F_124,H_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_266])).

tff(c_279,plain,(
    ! [C_29,D_30,B_28,H_125,A_27,E_31] : k5_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,H_125) = k2_xboole_0(k3_enumset1(A_27,B_28,C_29,D_30,E_31),k1_tarski(H_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_270])).

tff(c_283,plain,(
    ! [A_134,B_133,E_132,D_130,H_131,C_129] : k2_xboole_0(k3_enumset1(A_134,B_133,C_129,D_130,E_132),k1_tarski(H_131)) = k4_enumset1(A_134,B_133,C_129,D_130,E_132,H_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_279])).

tff(c_292,plain,(
    ! [H_131,A_23,B_24,D_26,C_25] : k4_enumset1(A_23,A_23,B_24,C_25,D_26,H_131) = k2_xboole_0(k2_enumset1(A_23,B_24,C_25,D_26),k1_tarski(H_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_283])).

tff(c_312,plain,(
    ! [C_143,H_144,D_146,B_145,A_147] : k2_xboole_0(k2_enumset1(A_147,B_145,C_143,D_146),k1_tarski(H_144)) = k3_enumset1(A_147,B_145,C_143,D_146,H_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_321,plain,(
    ! [A_20,B_21,C_22,H_144] : k3_enumset1(A_20,A_20,B_21,C_22,H_144) = k2_xboole_0(k1_enumset1(A_20,B_21,C_22),k1_tarski(H_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_312])).

tff(c_325,plain,(
    ! [A_148,B_149,C_150,H_151] : k2_xboole_0(k1_enumset1(A_148,B_149,C_150),k1_tarski(H_151)) = k2_enumset1(A_148,B_149,C_150,H_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_321])).

tff(c_334,plain,(
    ! [A_18,B_19,H_151] : k2_xboole_0(k2_tarski(A_18,B_19),k1_tarski(H_151)) = k2_enumset1(A_18,A_18,B_19,H_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_325])).

tff(c_338,plain,(
    ! [A_152,B_153,H_154] : k2_xboole_0(k2_tarski(A_152,B_153),k1_tarski(H_154)) = k1_enumset1(A_152,B_153,H_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_334])).

tff(c_347,plain,(
    ! [A_17,H_154] : k2_xboole_0(k1_tarski(A_17),k1_tarski(H_154)) = k1_enumset1(A_17,A_17,H_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_338])).

tff(c_350,plain,(
    ! [A_17,H_154] : k2_xboole_0(k1_tarski(A_17),k1_tarski(H_154)) = k2_tarski(A_17,H_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_347])).

tff(c_82,plain,(
    ! [A_63,B_64,C_65,D_66] : v1_relat_1(k2_tarski(k4_tarski(A_63,B_64),k4_tarski(C_65,D_66))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [A_63,B_64] : v1_relat_1(k1_tarski(k4_tarski(A_63,B_64))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_24,plain,(
    ! [A_48,B_49,C_50,D_51] : v1_relat_1(k2_tarski(k4_tarski(A_48,B_49),k4_tarski(C_50,D_51))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_52,B_53),k4_tarski(C_54,D_55))) = k2_tarski(B_53,D_55)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_52,B_53),k4_tarski(C_54,D_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_115,plain,(
    ! [A_77,B_78,C_79,D_80] : k2_relat_1(k2_tarski(k4_tarski(A_77,B_78),k4_tarski(C_79,D_80))) = k2_tarski(B_78,D_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_128,plain,(
    ! [B_78,A_77] : k2_tarski(B_78,B_78) = k2_relat_1(k1_tarski(k4_tarski(A_77,B_78))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_115])).

tff(c_133,plain,(
    ! [A_77,B_78] : k2_relat_1(k1_tarski(k4_tarski(A_77,B_78))) = k1_tarski(B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_28,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_52,B_53),k4_tarski(C_54,D_55))) = k2_tarski(A_52,C_54)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_52,B_53),k4_tarski(C_54,D_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_83,B_84,C_85,D_86] : k1_relat_1(k2_tarski(k4_tarski(A_83,B_84),k4_tarski(C_85,D_86))) = k2_tarski(A_83,C_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_161,plain,(
    ! [A_83,B_84] : k2_tarski(A_83,A_83) = k1_relat_1(k1_tarski(k4_tarski(A_83,B_84))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_148])).

tff(c_167,plain,(
    ! [A_87,B_88] : k1_relat_1(k1_tarski(k4_tarski(A_87,B_88))) = k1_tarski(A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_22,plain,(
    ! [A_47] :
      ( k2_xboole_0(k1_relat_1(A_47),k2_relat_1(A_47)) = k3_relat_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [A_87,B_88] :
      ( k2_xboole_0(k1_tarski(A_87),k2_relat_1(k1_tarski(k4_tarski(A_87,B_88)))) = k3_relat_1(k1_tarski(k4_tarski(A_87,B_88)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_87,B_88))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_22])).

tff(c_179,plain,(
    ! [A_87,B_88] : k2_xboole_0(k1_tarski(A_87),k1_tarski(B_88)) = k3_relat_1(k1_tarski(k4_tarski(A_87,B_88))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_133,c_173])).

tff(c_384,plain,(
    ! [A_87,B_88] : k3_relat_1(k1_tarski(k4_tarski(A_87,B_88))) = k2_tarski(A_87,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_179])).

tff(c_30,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  
% 2.18/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.32  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 2.18/1.32  
% 2.18/1.32  %Foreground sorts:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Background operators:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Foreground operators:
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.32  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.18/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.18/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.32  
% 2.50/1.34  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.50/1.34  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.50/1.34  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.50/1.34  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.50/1.34  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.50/1.34  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.50/1.34  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.50/1.34  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 2.50/1.34  tff(f_51, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.50/1.34  tff(f_59, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 2.50/1.34  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.50/1.34  tff(f_62, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 2.50/1.34  tff(c_8, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.34  tff(c_6, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.34  tff(c_10, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.34  tff(c_12, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.34  tff(c_14, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_enumset1(A_27, A_27, B_28, C_29, D_30, E_31)=k3_enumset1(A_27, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.34  tff(c_16, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k5_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37)=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.34  tff(c_18, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43, G_44)=k5_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.34  tff(c_257, plain, (![B_115, H_119, A_121, G_120, C_116, D_117, E_118, F_114]: (k2_xboole_0(k5_enumset1(A_121, B_115, C_116, D_117, E_118, F_114, G_120), k1_tarski(H_119))=k6_enumset1(A_121, B_115, C_116, D_117, E_118, F_114, G_120, H_119))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.34  tff(c_266, plain, (![B_33, C_34, H_119, E_36, F_37, A_32, D_35]: (k6_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37, H_119)=k2_xboole_0(k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37), k1_tarski(H_119)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_257])).
% 2.50/1.34  tff(c_270, plain, (![C_126, F_124, A_127, H_125, E_122, D_128, B_123]: (k2_xboole_0(k4_enumset1(A_127, B_123, C_126, D_128, E_122, F_124), k1_tarski(H_125))=k5_enumset1(A_127, B_123, C_126, D_128, E_122, F_124, H_125))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_266])).
% 2.50/1.34  tff(c_279, plain, (![C_29, D_30, B_28, H_125, A_27, E_31]: (k5_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, H_125)=k2_xboole_0(k3_enumset1(A_27, B_28, C_29, D_30, E_31), k1_tarski(H_125)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_270])).
% 2.50/1.34  tff(c_283, plain, (![A_134, B_133, E_132, D_130, H_131, C_129]: (k2_xboole_0(k3_enumset1(A_134, B_133, C_129, D_130, E_132), k1_tarski(H_131))=k4_enumset1(A_134, B_133, C_129, D_130, E_132, H_131))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_279])).
% 2.50/1.34  tff(c_292, plain, (![H_131, A_23, B_24, D_26, C_25]: (k4_enumset1(A_23, A_23, B_24, C_25, D_26, H_131)=k2_xboole_0(k2_enumset1(A_23, B_24, C_25, D_26), k1_tarski(H_131)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_283])).
% 2.50/1.34  tff(c_312, plain, (![C_143, H_144, D_146, B_145, A_147]: (k2_xboole_0(k2_enumset1(A_147, B_145, C_143, D_146), k1_tarski(H_144))=k3_enumset1(A_147, B_145, C_143, D_146, H_144))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_292])).
% 2.50/1.34  tff(c_321, plain, (![A_20, B_21, C_22, H_144]: (k3_enumset1(A_20, A_20, B_21, C_22, H_144)=k2_xboole_0(k1_enumset1(A_20, B_21, C_22), k1_tarski(H_144)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_312])).
% 2.50/1.34  tff(c_325, plain, (![A_148, B_149, C_150, H_151]: (k2_xboole_0(k1_enumset1(A_148, B_149, C_150), k1_tarski(H_151))=k2_enumset1(A_148, B_149, C_150, H_151))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_321])).
% 2.50/1.34  tff(c_334, plain, (![A_18, B_19, H_151]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_tarski(H_151))=k2_enumset1(A_18, A_18, B_19, H_151))), inference(superposition, [status(thm), theory('equality')], [c_8, c_325])).
% 2.50/1.34  tff(c_338, plain, (![A_152, B_153, H_154]: (k2_xboole_0(k2_tarski(A_152, B_153), k1_tarski(H_154))=k1_enumset1(A_152, B_153, H_154))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_334])).
% 2.50/1.34  tff(c_347, plain, (![A_17, H_154]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(H_154))=k1_enumset1(A_17, A_17, H_154))), inference(superposition, [status(thm), theory('equality')], [c_6, c_338])).
% 2.50/1.34  tff(c_350, plain, (![A_17, H_154]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(H_154))=k2_tarski(A_17, H_154))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_347])).
% 2.50/1.34  tff(c_82, plain, (![A_63, B_64, C_65, D_66]: (v1_relat_1(k2_tarski(k4_tarski(A_63, B_64), k4_tarski(C_65, D_66))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.50/1.34  tff(c_86, plain, (![A_63, B_64]: (v1_relat_1(k1_tarski(k4_tarski(A_63, B_64))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_82])).
% 2.50/1.34  tff(c_24, plain, (![A_48, B_49, C_50, D_51]: (v1_relat_1(k2_tarski(k4_tarski(A_48, B_49), k4_tarski(C_50, D_51))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.50/1.34  tff(c_26, plain, (![A_52, B_53, C_54, D_55]: (k2_relat_1(k2_tarski(k4_tarski(A_52, B_53), k4_tarski(C_54, D_55)))=k2_tarski(B_53, D_55) | ~v1_relat_1(k2_tarski(k4_tarski(A_52, B_53), k4_tarski(C_54, D_55))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.34  tff(c_115, plain, (![A_77, B_78, C_79, D_80]: (k2_relat_1(k2_tarski(k4_tarski(A_77, B_78), k4_tarski(C_79, D_80)))=k2_tarski(B_78, D_80))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.50/1.34  tff(c_128, plain, (![B_78, A_77]: (k2_tarski(B_78, B_78)=k2_relat_1(k1_tarski(k4_tarski(A_77, B_78))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_115])).
% 2.50/1.34  tff(c_133, plain, (![A_77, B_78]: (k2_relat_1(k1_tarski(k4_tarski(A_77, B_78)))=k1_tarski(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_128])).
% 2.50/1.34  tff(c_28, plain, (![A_52, B_53, C_54, D_55]: (k1_relat_1(k2_tarski(k4_tarski(A_52, B_53), k4_tarski(C_54, D_55)))=k2_tarski(A_52, C_54) | ~v1_relat_1(k2_tarski(k4_tarski(A_52, B_53), k4_tarski(C_54, D_55))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.50/1.34  tff(c_148, plain, (![A_83, B_84, C_85, D_86]: (k1_relat_1(k2_tarski(k4_tarski(A_83, B_84), k4_tarski(C_85, D_86)))=k2_tarski(A_83, C_85))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.50/1.34  tff(c_161, plain, (![A_83, B_84]: (k2_tarski(A_83, A_83)=k1_relat_1(k1_tarski(k4_tarski(A_83, B_84))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_148])).
% 2.50/1.34  tff(c_167, plain, (![A_87, B_88]: (k1_relat_1(k1_tarski(k4_tarski(A_87, B_88)))=k1_tarski(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_161])).
% 2.50/1.34  tff(c_22, plain, (![A_47]: (k2_xboole_0(k1_relat_1(A_47), k2_relat_1(A_47))=k3_relat_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.34  tff(c_173, plain, (![A_87, B_88]: (k2_xboole_0(k1_tarski(A_87), k2_relat_1(k1_tarski(k4_tarski(A_87, B_88))))=k3_relat_1(k1_tarski(k4_tarski(A_87, B_88))) | ~v1_relat_1(k1_tarski(k4_tarski(A_87, B_88))))), inference(superposition, [status(thm), theory('equality')], [c_167, c_22])).
% 2.50/1.34  tff(c_179, plain, (![A_87, B_88]: (k2_xboole_0(k1_tarski(A_87), k1_tarski(B_88))=k3_relat_1(k1_tarski(k4_tarski(A_87, B_88))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_133, c_173])).
% 2.50/1.34  tff(c_384, plain, (![A_87, B_88]: (k3_relat_1(k1_tarski(k4_tarski(A_87, B_88)))=k2_tarski(A_87, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_179])).
% 2.50/1.34  tff(c_30, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.50/1.34  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_384, c_30])).
% 2.50/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  Inference rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Ref     : 0
% 2.50/1.34  #Sup     : 87
% 2.50/1.34  #Fact    : 0
% 2.50/1.34  #Define  : 0
% 2.50/1.34  #Split   : 0
% 2.50/1.34  #Chain   : 0
% 2.50/1.34  #Close   : 0
% 2.50/1.34  
% 2.50/1.34  Ordering : KBO
% 2.50/1.34  
% 2.50/1.34  Simplification rules
% 2.50/1.34  ----------------------
% 2.50/1.34  #Subsume      : 1
% 2.50/1.34  #Demod        : 30
% 2.50/1.34  #Tautology    : 65
% 2.50/1.34  #SimpNegUnit  : 0
% 2.50/1.34  #BackRed      : 3
% 2.50/1.34  
% 2.50/1.34  #Partial instantiations: 0
% 2.50/1.34  #Strategies tried      : 1
% 2.50/1.34  
% 2.50/1.34  Timing (in seconds)
% 2.50/1.34  ----------------------
% 2.50/1.34  Preprocessing        : 0.33
% 2.50/1.34  Parsing              : 0.17
% 2.50/1.34  CNF conversion       : 0.02
% 2.50/1.34  Main loop            : 0.24
% 2.50/1.34  Inferencing          : 0.11
% 2.50/1.34  Reduction            : 0.09
% 2.50/1.34  Demodulation         : 0.07
% 2.50/1.34  BG Simplification    : 0.02
% 2.50/1.34  Subsumption          : 0.02
% 2.50/1.34  Abstraction          : 0.02
% 2.50/1.34  MUC search           : 0.00
% 2.50/1.34  Cooper               : 0.00
% 2.50/1.34  Total                : 0.61
% 2.50/1.34  Index Insertion      : 0.00
% 2.50/1.34  Index Deletion       : 0.00
% 2.50/1.34  Index Matching       : 0.00
% 2.50/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
