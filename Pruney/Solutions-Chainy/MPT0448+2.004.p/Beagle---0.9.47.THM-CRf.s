%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   64 (  87 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :   52 (  78 expanded)
%              Number of equality atoms :   42 (  61 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_6,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k6_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35,G_36) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [A_98,E_94,G_93,D_95,F_92,H_99,C_97,B_96] : k2_xboole_0(k5_enumset1(A_98,B_96,C_97,D_95,E_94,F_92,G_93),k1_tarski(H_99)) = k6_enumset1(A_98,B_96,C_97,D_95,E_94,F_92,G_93,H_99) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,H_99,E_28] : k6_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29,H_99) = k2_xboole_0(k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29),k1_tarski(H_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_203])).

tff(c_216,plain,(
    ! [A_104,B_101,C_100,H_105,F_103,E_102,D_106] : k2_xboole_0(k4_enumset1(A_104,B_101,C_100,D_106,E_102,F_103),k1_tarski(H_105)) = k5_enumset1(A_104,B_101,C_100,D_106,E_102,F_103,H_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_225,plain,(
    ! [A_19,C_21,D_22,B_20,H_105,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,H_105) = k2_xboole_0(k3_enumset1(A_19,B_20,C_21,D_22,E_23),k1_tarski(H_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_229,plain,(
    ! [E_108,H_109,B_110,A_111,D_112,C_107] : k2_xboole_0(k3_enumset1(A_111,B_110,C_107,D_112,E_108),k1_tarski(H_109)) = k4_enumset1(A_111,B_110,C_107,D_112,E_108,H_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_225])).

tff(c_238,plain,(
    ! [B_16,A_15,H_109,D_18,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,H_109) = k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_tarski(H_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_229])).

tff(c_242,plain,(
    ! [A_117,D_114,H_115,B_116,C_113] : k2_xboole_0(k2_enumset1(A_117,B_116,C_113,D_114),k1_tarski(H_115)) = k3_enumset1(A_117,B_116,C_113,D_114,H_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_238])).

tff(c_251,plain,(
    ! [A_12,B_13,C_14,H_115] : k3_enumset1(A_12,A_12,B_13,C_14,H_115) = k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(H_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_242])).

tff(c_255,plain,(
    ! [A_118,B_119,C_120,H_121] : k2_xboole_0(k1_enumset1(A_118,B_119,C_120),k1_tarski(H_121)) = k2_enumset1(A_118,B_119,C_120,H_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_251])).

tff(c_264,plain,(
    ! [A_10,B_11,H_121] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(H_121)) = k2_enumset1(A_10,A_10,B_11,H_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_255])).

tff(c_268,plain,(
    ! [A_122,B_123,H_124] : k2_xboole_0(k2_tarski(A_122,B_123),k1_tarski(H_124)) = k1_enumset1(A_122,B_123,H_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_264])).

tff(c_277,plain,(
    ! [A_9,H_124] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_124)) = k1_enumset1(A_9,A_9,H_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_268])).

tff(c_280,plain,(
    ! [A_9,H_124] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_124)) = k2_tarski(A_9,H_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_277])).

tff(c_76,plain,(
    ! [A_53,B_54,C_55,D_56] : v1_relat_1(k2_tarski(k4_tarski(A_53,B_54),k4_tarski(C_55,D_56))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,(
    ! [A_53,B_54] : v1_relat_1(k1_tarski(k4_tarski(A_53,B_54))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_24,plain,(
    ! [A_44,B_45] :
      ( k2_relat_1(k1_tarski(k4_tarski(A_44,B_45))) = k1_tarski(B_45)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,(
    ! [A_44,B_45] : k2_relat_1(k1_tarski(k4_tarski(A_44,B_45))) = k1_tarski(B_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24])).

tff(c_26,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_44,B_45))) = k1_tarski(A_44)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_127,plain,(
    ! [A_69,B_70] : k1_relat_1(k1_tarski(k4_tarski(A_69,B_70))) = k1_tarski(A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_20,plain,(
    ! [A_39] :
      ( k2_xboole_0(k1_relat_1(A_39),k2_relat_1(A_39)) = k3_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(k1_tarski(A_69),k2_relat_1(k1_tarski(k4_tarski(A_69,B_70)))) = k3_relat_1(k1_tarski(k4_tarski(A_69,B_70)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_69,B_70))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_20])).

tff(c_139,plain,(
    ! [A_69,B_70] : k2_xboole_0(k1_tarski(A_69),k1_tarski(B_70)) = k3_relat_1(k1_tarski(k4_tarski(A_69,B_70))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_110,c_133])).

tff(c_281,plain,(
    ! [A_69,B_70] : k3_relat_1(k1_tarski(k4_tarski(A_69,B_70))) = k2_tarski(A_69,B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_139])).

tff(c_28,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.14/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.14/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.28  
% 2.14/1.30  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.14/1.30  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.30  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.14/1.30  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.14/1.30  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.14/1.30  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.14/1.30  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.14/1.30  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 2.14/1.30  tff(f_49, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.14/1.30  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 2.14/1.30  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.14/1.30  tff(f_60, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 2.14/1.30  tff(c_6, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.30  tff(c_4, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.30  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.30  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.30  tff(c_12, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.30  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k6_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35, G_36)=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.30  tff(c_203, plain, (![A_98, E_94, G_93, D_95, F_92, H_99, C_97, B_96]: (k2_xboole_0(k5_enumset1(A_98, B_96, C_97, D_95, E_94, F_92, G_93), k1_tarski(H_99))=k6_enumset1(A_98, B_96, C_97, D_95, E_94, F_92, G_93, H_99))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.30  tff(c_212, plain, (![A_24, B_25, F_29, D_27, C_26, H_99, E_28]: (k6_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29, H_99)=k2_xboole_0(k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29), k1_tarski(H_99)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_203])).
% 2.14/1.30  tff(c_216, plain, (![A_104, B_101, C_100, H_105, F_103, E_102, D_106]: (k2_xboole_0(k4_enumset1(A_104, B_101, C_100, D_106, E_102, F_103), k1_tarski(H_105))=k5_enumset1(A_104, B_101, C_100, D_106, E_102, F_103, H_105))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_212])).
% 2.14/1.30  tff(c_225, plain, (![A_19, C_21, D_22, B_20, H_105, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, H_105)=k2_xboole_0(k3_enumset1(A_19, B_20, C_21, D_22, E_23), k1_tarski(H_105)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_216])).
% 2.14/1.30  tff(c_229, plain, (![E_108, H_109, B_110, A_111, D_112, C_107]: (k2_xboole_0(k3_enumset1(A_111, B_110, C_107, D_112, E_108), k1_tarski(H_109))=k4_enumset1(A_111, B_110, C_107, D_112, E_108, H_109))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_225])).
% 2.14/1.30  tff(c_238, plain, (![B_16, A_15, H_109, D_18, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, H_109)=k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_tarski(H_109)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_229])).
% 2.14/1.30  tff(c_242, plain, (![A_117, D_114, H_115, B_116, C_113]: (k2_xboole_0(k2_enumset1(A_117, B_116, C_113, D_114), k1_tarski(H_115))=k3_enumset1(A_117, B_116, C_113, D_114, H_115))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_238])).
% 2.14/1.30  tff(c_251, plain, (![A_12, B_13, C_14, H_115]: (k3_enumset1(A_12, A_12, B_13, C_14, H_115)=k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(H_115)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_242])).
% 2.14/1.30  tff(c_255, plain, (![A_118, B_119, C_120, H_121]: (k2_xboole_0(k1_enumset1(A_118, B_119, C_120), k1_tarski(H_121))=k2_enumset1(A_118, B_119, C_120, H_121))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_251])).
% 2.14/1.30  tff(c_264, plain, (![A_10, B_11, H_121]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(H_121))=k2_enumset1(A_10, A_10, B_11, H_121))), inference(superposition, [status(thm), theory('equality')], [c_6, c_255])).
% 2.14/1.30  tff(c_268, plain, (![A_122, B_123, H_124]: (k2_xboole_0(k2_tarski(A_122, B_123), k1_tarski(H_124))=k1_enumset1(A_122, B_123, H_124))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_264])).
% 2.14/1.30  tff(c_277, plain, (![A_9, H_124]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_124))=k1_enumset1(A_9, A_9, H_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_268])).
% 2.14/1.30  tff(c_280, plain, (![A_9, H_124]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_124))=k2_tarski(A_9, H_124))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_277])).
% 2.14/1.30  tff(c_76, plain, (![A_53, B_54, C_55, D_56]: (v1_relat_1(k2_tarski(k4_tarski(A_53, B_54), k4_tarski(C_55, D_56))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.30  tff(c_80, plain, (![A_53, B_54]: (v1_relat_1(k1_tarski(k4_tarski(A_53, B_54))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_76])).
% 2.14/1.30  tff(c_24, plain, (![A_44, B_45]: (k2_relat_1(k1_tarski(k4_tarski(A_44, B_45)))=k1_tarski(B_45) | ~v1_relat_1(k1_tarski(k4_tarski(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.30  tff(c_110, plain, (![A_44, B_45]: (k2_relat_1(k1_tarski(k4_tarski(A_44, B_45)))=k1_tarski(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24])).
% 2.14/1.30  tff(c_26, plain, (![A_44, B_45]: (k1_relat_1(k1_tarski(k4_tarski(A_44, B_45)))=k1_tarski(A_44) | ~v1_relat_1(k1_tarski(k4_tarski(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.30  tff(c_127, plain, (![A_69, B_70]: (k1_relat_1(k1_tarski(k4_tarski(A_69, B_70)))=k1_tarski(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_26])).
% 2.14/1.30  tff(c_20, plain, (![A_39]: (k2_xboole_0(k1_relat_1(A_39), k2_relat_1(A_39))=k3_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.30  tff(c_133, plain, (![A_69, B_70]: (k2_xboole_0(k1_tarski(A_69), k2_relat_1(k1_tarski(k4_tarski(A_69, B_70))))=k3_relat_1(k1_tarski(k4_tarski(A_69, B_70))) | ~v1_relat_1(k1_tarski(k4_tarski(A_69, B_70))))), inference(superposition, [status(thm), theory('equality')], [c_127, c_20])).
% 2.14/1.30  tff(c_139, plain, (![A_69, B_70]: (k2_xboole_0(k1_tarski(A_69), k1_tarski(B_70))=k3_relat_1(k1_tarski(k4_tarski(A_69, B_70))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_110, c_133])).
% 2.14/1.30  tff(c_281, plain, (![A_69, B_70]: (k3_relat_1(k1_tarski(k4_tarski(A_69, B_70)))=k2_tarski(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_139])).
% 2.14/1.30  tff(c_28, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.14/1.30  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_28])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 64
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 0
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 1
% 2.14/1.30  #Demod        : 19
% 2.14/1.30  #Tautology    : 52
% 2.14/1.30  #SimpNegUnit  : 0
% 2.14/1.30  #BackRed      : 3
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.30  Preprocessing        : 0.33
% 2.14/1.30  Parsing              : 0.18
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.19
% 2.14/1.30  Inferencing          : 0.08
% 2.14/1.30  Reduction            : 0.06
% 2.14/1.30  Demodulation         : 0.05
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.02
% 2.14/1.30  Abstraction          : 0.02
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.55
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
