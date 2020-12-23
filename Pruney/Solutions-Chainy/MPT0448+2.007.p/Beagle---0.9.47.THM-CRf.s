%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:36 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   65 (  87 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :   53 (  78 expanded)
%              Number of equality atoms :   42 (  63 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_8,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_22,B_23,C_24,D_25] : k3_enumset1(A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,E_30) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] : k5_enumset1(A_31,A_31,B_32,C_33,D_34,E_35,F_36) = k4_enumset1(A_31,B_32,C_33,D_34,E_35,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_257,plain,(
    ! [E_115,F_113,D_116,A_119,G_114,C_118,B_117] : k2_xboole_0(k4_enumset1(A_119,B_117,C_118,D_116,E_115,F_113),k1_tarski(G_114)) = k5_enumset1(A_119,B_117,C_118,D_116,E_115,F_113,G_114) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_266,plain,(
    ! [B_27,D_29,A_26,E_30,G_114,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,E_30,G_114) = k2_xboole_0(k3_enumset1(A_26,B_27,C_28,D_29,E_30),k1_tarski(G_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_257])).

tff(c_270,plain,(
    ! [B_122,G_120,A_123,D_121,E_125,C_124] : k2_xboole_0(k3_enumset1(A_123,B_122,C_124,D_121,E_125),k1_tarski(G_120)) = k4_enumset1(A_123,B_122,C_124,D_121,E_125,G_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_266])).

tff(c_279,plain,(
    ! [G_120,A_22,B_23,D_25,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,D_25,G_120) = k2_xboole_0(k2_enumset1(A_22,B_23,C_24,D_25),k1_tarski(G_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_270])).

tff(c_283,plain,(
    ! [G_129,A_126,B_130,C_127,D_128] : k2_xboole_0(k2_enumset1(A_126,B_130,C_127,D_128),k1_tarski(G_129)) = k3_enumset1(A_126,B_130,C_127,D_128,G_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_279])).

tff(c_292,plain,(
    ! [A_19,B_20,C_21,G_129] : k3_enumset1(A_19,A_19,B_20,C_21,G_129) = k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(G_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_283])).

tff(c_313,plain,(
    ! [A_139,B_140,C_141,G_142] : k2_xboole_0(k1_enumset1(A_139,B_140,C_141),k1_tarski(G_142)) = k2_enumset1(A_139,B_140,C_141,G_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_292])).

tff(c_322,plain,(
    ! [A_17,B_18,G_142] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(G_142)) = k2_enumset1(A_17,A_17,B_18,G_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_313])).

tff(c_326,plain,(
    ! [A_143,B_144,G_145] : k2_xboole_0(k2_tarski(A_143,B_144),k1_tarski(G_145)) = k1_enumset1(A_143,B_144,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_322])).

tff(c_335,plain,(
    ! [A_16,G_145] : k2_xboole_0(k1_tarski(A_16),k1_tarski(G_145)) = k1_enumset1(A_16,A_16,G_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_326])).

tff(c_338,plain,(
    ! [A_16,G_145] : k2_xboole_0(k1_tarski(A_16),k1_tarski(G_145)) = k2_tarski(A_16,G_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_335])).

tff(c_82,plain,(
    ! [A_62,B_63,C_64,D_65] : v1_relat_1(k2_tarski(k4_tarski(A_62,B_63),k4_tarski(C_64,D_65))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [A_62,B_63] : v1_relat_1(k1_tarski(k4_tarski(A_62,B_63))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_82])).

tff(c_24,plain,(
    ! [A_47,B_48,C_49,D_50] : v1_relat_1(k2_tarski(k4_tarski(A_47,B_48),k4_tarski(C_49,D_50))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_51,B_52),k4_tarski(C_53,D_54))) = k2_tarski(B_52,D_54)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_51,B_52),k4_tarski(C_53,D_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_115,plain,(
    ! [A_76,B_77,C_78,D_79] : k2_relat_1(k2_tarski(k4_tarski(A_76,B_77),k4_tarski(C_78,D_79))) = k2_tarski(B_77,D_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_128,plain,(
    ! [B_77,A_76] : k2_tarski(B_77,B_77) = k2_relat_1(k1_tarski(k4_tarski(A_76,B_77))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_115])).

tff(c_133,plain,(
    ! [A_76,B_77] : k2_relat_1(k1_tarski(k4_tarski(A_76,B_77))) = k1_tarski(B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128])).

tff(c_28,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_51,B_52),k4_tarski(C_53,D_54))) = k2_tarski(A_51,C_53)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_51,B_52),k4_tarski(C_53,D_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_82,B_83,C_84,D_85] : k1_relat_1(k2_tarski(k4_tarski(A_82,B_83),k4_tarski(C_84,D_85))) = k2_tarski(A_82,C_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_161,plain,(
    ! [A_82,B_83] : k2_tarski(A_82,A_82) = k1_relat_1(k1_tarski(k4_tarski(A_82,B_83))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_148])).

tff(c_167,plain,(
    ! [A_86,B_87] : k1_relat_1(k1_tarski(k4_tarski(A_86,B_87))) = k1_tarski(A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_22,plain,(
    ! [A_46] :
      ( k2_xboole_0(k1_relat_1(A_46),k2_relat_1(A_46)) = k3_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [A_86,B_87] :
      ( k2_xboole_0(k1_tarski(A_86),k2_relat_1(k1_tarski(k4_tarski(A_86,B_87)))) = k3_relat_1(k1_tarski(k4_tarski(A_86,B_87)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_86,B_87))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_22])).

tff(c_179,plain,(
    ! [A_86,B_87] : k2_xboole_0(k1_tarski(A_86),k1_tarski(B_87)) = k3_relat_1(k1_tarski(k4_tarski(A_86,B_87))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_133,c_173])).

tff(c_339,plain,(
    ! [A_86,B_87] : k3_relat_1(k1_tarski(k4_tarski(A_86,B_87))) = k2_tarski(A_86,B_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_179])).

tff(c_30,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.30  
% 2.27/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.30  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 2.27/1.30  
% 2.27/1.30  %Foreground sorts:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Background operators:
% 2.27/1.30  
% 2.27/1.30  
% 2.27/1.30  %Foreground operators:
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.30  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.27/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.27/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.30  
% 2.27/1.31  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.27/1.31  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.31  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.27/1.31  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.27/1.31  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.27/1.31  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.27/1.31  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.27/1.31  tff(f_51, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.27/1.31  tff(f_59, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 2.27/1.31  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.27/1.31  tff(f_62, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relat_1)).
% 2.27/1.31  tff(c_8, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.32  tff(c_6, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.32  tff(c_10, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.32  tff(c_12, plain, (![A_22, B_23, C_24, D_25]: (k3_enumset1(A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.32  tff(c_14, plain, (![B_27, D_29, A_26, E_30, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, E_30)=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.32  tff(c_16, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (k5_enumset1(A_31, A_31, B_32, C_33, D_34, E_35, F_36)=k4_enumset1(A_31, B_32, C_33, D_34, E_35, F_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.32  tff(c_257, plain, (![E_115, F_113, D_116, A_119, G_114, C_118, B_117]: (k2_xboole_0(k4_enumset1(A_119, B_117, C_118, D_116, E_115, F_113), k1_tarski(G_114))=k5_enumset1(A_119, B_117, C_118, D_116, E_115, F_113, G_114))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.32  tff(c_266, plain, (![B_27, D_29, A_26, E_30, G_114, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, E_30, G_114)=k2_xboole_0(k3_enumset1(A_26, B_27, C_28, D_29, E_30), k1_tarski(G_114)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_257])).
% 2.27/1.32  tff(c_270, plain, (![B_122, G_120, A_123, D_121, E_125, C_124]: (k2_xboole_0(k3_enumset1(A_123, B_122, C_124, D_121, E_125), k1_tarski(G_120))=k4_enumset1(A_123, B_122, C_124, D_121, E_125, G_120))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_266])).
% 2.27/1.32  tff(c_279, plain, (![G_120, A_22, B_23, D_25, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, D_25, G_120)=k2_xboole_0(k2_enumset1(A_22, B_23, C_24, D_25), k1_tarski(G_120)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_270])).
% 2.27/1.32  tff(c_283, plain, (![G_129, A_126, B_130, C_127, D_128]: (k2_xboole_0(k2_enumset1(A_126, B_130, C_127, D_128), k1_tarski(G_129))=k3_enumset1(A_126, B_130, C_127, D_128, G_129))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_279])).
% 2.27/1.32  tff(c_292, plain, (![A_19, B_20, C_21, G_129]: (k3_enumset1(A_19, A_19, B_20, C_21, G_129)=k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(G_129)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_283])).
% 2.27/1.32  tff(c_313, plain, (![A_139, B_140, C_141, G_142]: (k2_xboole_0(k1_enumset1(A_139, B_140, C_141), k1_tarski(G_142))=k2_enumset1(A_139, B_140, C_141, G_142))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_292])).
% 2.27/1.32  tff(c_322, plain, (![A_17, B_18, G_142]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(G_142))=k2_enumset1(A_17, A_17, B_18, G_142))), inference(superposition, [status(thm), theory('equality')], [c_8, c_313])).
% 2.27/1.32  tff(c_326, plain, (![A_143, B_144, G_145]: (k2_xboole_0(k2_tarski(A_143, B_144), k1_tarski(G_145))=k1_enumset1(A_143, B_144, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_322])).
% 2.27/1.32  tff(c_335, plain, (![A_16, G_145]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(G_145))=k1_enumset1(A_16, A_16, G_145))), inference(superposition, [status(thm), theory('equality')], [c_6, c_326])).
% 2.27/1.32  tff(c_338, plain, (![A_16, G_145]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(G_145))=k2_tarski(A_16, G_145))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_335])).
% 2.27/1.32  tff(c_82, plain, (![A_62, B_63, C_64, D_65]: (v1_relat_1(k2_tarski(k4_tarski(A_62, B_63), k4_tarski(C_64, D_65))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.27/1.32  tff(c_86, plain, (![A_62, B_63]: (v1_relat_1(k1_tarski(k4_tarski(A_62, B_63))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_82])).
% 2.27/1.32  tff(c_24, plain, (![A_47, B_48, C_49, D_50]: (v1_relat_1(k2_tarski(k4_tarski(A_47, B_48), k4_tarski(C_49, D_50))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.27/1.32  tff(c_26, plain, (![A_51, B_52, C_53, D_54]: (k2_relat_1(k2_tarski(k4_tarski(A_51, B_52), k4_tarski(C_53, D_54)))=k2_tarski(B_52, D_54) | ~v1_relat_1(k2_tarski(k4_tarski(A_51, B_52), k4_tarski(C_53, D_54))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.32  tff(c_115, plain, (![A_76, B_77, C_78, D_79]: (k2_relat_1(k2_tarski(k4_tarski(A_76, B_77), k4_tarski(C_78, D_79)))=k2_tarski(B_77, D_79))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.27/1.32  tff(c_128, plain, (![B_77, A_76]: (k2_tarski(B_77, B_77)=k2_relat_1(k1_tarski(k4_tarski(A_76, B_77))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_115])).
% 2.27/1.32  tff(c_133, plain, (![A_76, B_77]: (k2_relat_1(k1_tarski(k4_tarski(A_76, B_77)))=k1_tarski(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_128])).
% 2.27/1.32  tff(c_28, plain, (![A_51, B_52, C_53, D_54]: (k1_relat_1(k2_tarski(k4_tarski(A_51, B_52), k4_tarski(C_53, D_54)))=k2_tarski(A_51, C_53) | ~v1_relat_1(k2_tarski(k4_tarski(A_51, B_52), k4_tarski(C_53, D_54))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.32  tff(c_148, plain, (![A_82, B_83, C_84, D_85]: (k1_relat_1(k2_tarski(k4_tarski(A_82, B_83), k4_tarski(C_84, D_85)))=k2_tarski(A_82, C_84))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.27/1.32  tff(c_161, plain, (![A_82, B_83]: (k2_tarski(A_82, A_82)=k1_relat_1(k1_tarski(k4_tarski(A_82, B_83))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_148])).
% 2.27/1.32  tff(c_167, plain, (![A_86, B_87]: (k1_relat_1(k1_tarski(k4_tarski(A_86, B_87)))=k1_tarski(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_161])).
% 2.27/1.32  tff(c_22, plain, (![A_46]: (k2_xboole_0(k1_relat_1(A_46), k2_relat_1(A_46))=k3_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.32  tff(c_173, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), k2_relat_1(k1_tarski(k4_tarski(A_86, B_87))))=k3_relat_1(k1_tarski(k4_tarski(A_86, B_87))) | ~v1_relat_1(k1_tarski(k4_tarski(A_86, B_87))))), inference(superposition, [status(thm), theory('equality')], [c_167, c_22])).
% 2.27/1.32  tff(c_179, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), k1_tarski(B_87))=k3_relat_1(k1_tarski(k4_tarski(A_86, B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_133, c_173])).
% 2.27/1.32  tff(c_339, plain, (![A_86, B_87]: (k3_relat_1(k1_tarski(k4_tarski(A_86, B_87)))=k2_tarski(A_86, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_338, c_179])).
% 2.27/1.32  tff(c_30, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.27/1.32  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_339, c_30])).
% 2.27/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  Inference rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Ref     : 0
% 2.27/1.32  #Sup     : 80
% 2.27/1.32  #Fact    : 0
% 2.27/1.32  #Define  : 0
% 2.27/1.32  #Split   : 0
% 2.27/1.32  #Chain   : 0
% 2.27/1.32  #Close   : 0
% 2.27/1.32  
% 2.27/1.32  Ordering : KBO
% 2.27/1.32  
% 2.27/1.32  Simplification rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Subsume      : 1
% 2.27/1.32  #Demod        : 30
% 2.27/1.32  #Tautology    : 61
% 2.27/1.32  #SimpNegUnit  : 0
% 2.27/1.32  #BackRed      : 3
% 2.27/1.32  
% 2.27/1.32  #Partial instantiations: 0
% 2.27/1.32  #Strategies tried      : 1
% 2.27/1.32  
% 2.27/1.32  Timing (in seconds)
% 2.27/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.33
% 2.27/1.32  Parsing              : 0.17
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.22
% 2.27/1.32  Inferencing          : 0.10
% 2.27/1.32  Reduction            : 0.08
% 2.27/1.32  Demodulation         : 0.06
% 2.27/1.32  BG Simplification    : 0.02
% 2.47/1.32  Subsumption          : 0.02
% 2.47/1.32  Abstraction          : 0.02
% 2.47/1.32  MUC search           : 0.00
% 2.47/1.32  Cooper               : 0.00
% 2.47/1.32  Total                : 0.58
% 2.47/1.32  Index Insertion      : 0.00
% 2.47/1.32  Index Deletion       : 0.00
% 2.47/1.32  Index Matching       : 0.00
% 2.47/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
