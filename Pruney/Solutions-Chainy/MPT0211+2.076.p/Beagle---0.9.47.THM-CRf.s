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
% DateTime   : Thu Dec  3 09:47:25 EST 2020

% Result     : Theorem 13.32s
% Output     : CNFRefutation 13.32s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 260 expanded)
%              Number of leaves         :   29 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :   47 ( 242 expanded)
%              Number of equality atoms :   46 ( 241 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_16,plain,(
    ! [D_25,C_24,B_23,A_22] : k2_enumset1(D_25,C_24,B_23,A_22) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_346,plain,(
    ! [B_92,D_93,C_94,A_95] : k2_enumset1(B_92,D_93,C_94,A_95) = k2_enumset1(A_95,B_92,C_94,D_93) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_48,B_49,C_50] : k2_enumset1(A_48,A_48,B_49,C_50) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_466,plain,(
    ! [B_96,D_97,C_98] : k2_enumset1(B_96,D_97,C_98,B_96) = k1_enumset1(B_96,C_98,D_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_28])).

tff(c_918,plain,(
    ! [A_113,B_114,C_115] : k2_enumset1(A_113,B_114,C_115,A_113) = k1_enumset1(A_113,B_114,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_466])).

tff(c_402,plain,(
    ! [B_92,D_93,C_94] : k2_enumset1(B_92,D_93,C_94,B_92) = k1_enumset1(B_92,C_94,D_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_28])).

tff(c_934,plain,(
    ! [A_113,C_115,B_114] : k1_enumset1(A_113,C_115,B_114) = k1_enumset1(A_113,B_114,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_402])).

tff(c_10,plain,(
    ! [A_10,C_12,B_11,D_13] : k2_enumset1(A_10,C_12,B_11,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [A_51,B_52,C_53,D_54] : k3_enumset1(A_51,A_51,B_52,C_53,D_54) = k2_enumset1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [B_56,E_59,C_57,A_55,D_58] : k4_enumset1(A_55,A_55,B_56,C_57,D_58,E_59) = k3_enumset1(A_55,B_56,C_57,D_58,E_59) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1592,plain,(
    ! [D_148,B_149,F_152,C_153,E_150,A_151] : k2_xboole_0(k2_enumset1(A_151,B_149,C_153,D_148),k2_tarski(E_150,F_152)) = k4_enumset1(A_151,B_149,C_153,D_148,E_150,F_152) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1649,plain,(
    ! [B_49,A_48,C_50,F_152,E_150] : k4_enumset1(A_48,A_48,B_49,C_50,E_150,F_152) = k2_xboole_0(k1_enumset1(A_48,B_49,C_50),k2_tarski(E_150,F_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1592])).

tff(c_8153,plain,(
    ! [E_244,F_245,C_243,A_242,B_241] : k2_xboole_0(k1_enumset1(A_242,B_241,C_243),k2_tarski(E_244,F_245)) = k3_enumset1(A_242,B_241,C_243,E_244,F_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1649])).

tff(c_8177,plain,(
    ! [A_46,B_47,E_244,F_245] : k3_enumset1(A_46,A_46,B_47,E_244,F_245) = k2_xboole_0(k2_tarski(A_46,B_47),k2_tarski(E_244,F_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8153])).

tff(c_8183,plain,(
    ! [A_46,B_47,E_244,F_245] : k2_xboole_0(k2_tarski(A_46,B_47),k2_tarski(E_244,F_245)) = k2_enumset1(A_46,B_47,E_244,F_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8177])).

tff(c_82,plain,(
    ! [D_76,C_77,B_78,A_79] : k2_enumset1(D_76,C_77,B_78,A_79) = k2_enumset1(A_79,B_78,C_77,D_76) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [D_76,C_77,B_78] : k2_enumset1(D_76,C_77,B_78,B_78) = k1_enumset1(B_78,C_77,D_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_28])).

tff(c_1514,plain,(
    ! [C_140,D_137,A_139,B_138,E_141] : k2_xboole_0(k2_enumset1(A_139,B_138,C_140,D_137),k1_tarski(E_141)) = k3_enumset1(A_139,B_138,C_140,D_137,E_141) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1571,plain,(
    ! [A_48,B_49,C_50,E_141] : k3_enumset1(A_48,A_48,B_49,C_50,E_141) = k2_xboole_0(k1_enumset1(A_48,B_49,C_50),k1_tarski(E_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1514])).

tff(c_1574,plain,(
    ! [A_48,B_49,C_50,E_141] : k2_xboole_0(k1_enumset1(A_48,B_49,C_50),k1_tarski(E_141)) = k2_enumset1(A_48,B_49,C_50,E_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1571])).

tff(c_24,plain,(
    ! [A_45] : k2_tarski(A_45,A_45) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8180,plain,(
    ! [A_242,B_241,C_243,A_45] : k3_enumset1(A_242,B_241,C_243,A_45,A_45) = k2_xboole_0(k1_enumset1(A_242,B_241,C_243),k1_tarski(A_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8153])).

tff(c_10747,plain,(
    ! [A_324,B_325,C_326,A_327] : k3_enumset1(A_324,B_325,C_326,A_327,A_327) = k2_enumset1(A_324,B_325,C_326,A_327) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_8180])).

tff(c_10760,plain,(
    ! [B_325,C_326,A_327] : k2_enumset1(B_325,C_326,A_327,A_327) = k2_enumset1(B_325,B_325,C_326,A_327) ),
    inference(superposition,[status(thm),theory(equality)],[c_10747,c_30])).

tff(c_10780,plain,(
    ! [B_328,C_329,A_330] : k1_enumset1(B_328,C_329,A_330) = k1_enumset1(A_330,C_329,B_328) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28,c_10760])).

tff(c_129,plain,(
    ! [D_80,C_81,B_82] : k2_enumset1(D_80,C_81,B_82,B_82) = k1_enumset1(B_82,C_81,D_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_28])).

tff(c_142,plain,(
    ! [C_81,B_82] : k1_enumset1(C_81,B_82,B_82) = k1_enumset1(B_82,C_81,C_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_28])).

tff(c_10820,plain,(
    ! [B_328,A_330] : k1_enumset1(B_328,B_328,A_330) = k1_enumset1(B_328,A_330,A_330) ),
    inference(superposition,[status(thm),theory(equality)],[c_10780,c_142])).

tff(c_10887,plain,(
    ! [B_328,A_330] : k1_enumset1(B_328,A_330,A_330) = k2_tarski(B_328,A_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10820])).

tff(c_10899,plain,(
    ! [C_81,B_82] : k2_tarski(C_81,B_82) = k2_tarski(B_82,C_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10887,c_10887,c_142])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1037,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_36])).

tff(c_10950,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10899,c_10899,c_1037])).

tff(c_26120,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8183,c_10950])).

tff(c_26123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_28,c_10,c_26120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.32/5.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/5.96  
% 13.32/5.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/5.96  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 13.32/5.96  
% 13.32/5.96  %Foreground sorts:
% 13.32/5.96  
% 13.32/5.96  
% 13.32/5.96  %Background operators:
% 13.32/5.96  
% 13.32/5.96  
% 13.32/5.96  %Foreground operators:
% 13.32/5.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.32/5.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.32/5.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.32/5.96  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.32/5.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.32/5.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.32/5.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.32/5.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.32/5.96  tff('#skF_2', type, '#skF_2': $i).
% 13.32/5.96  tff('#skF_3', type, '#skF_3': $i).
% 13.32/5.96  tff('#skF_1', type, '#skF_1': $i).
% 13.32/5.96  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.32/5.96  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.32/5.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.32/5.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.32/5.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.32/5.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.32/5.96  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.32/5.96  
% 13.32/5.98  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 13.32/5.98  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 13.32/5.98  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 13.32/5.98  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 13.32/5.98  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 13.32/5.98  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.32/5.98  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 13.32/5.98  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 13.32/5.98  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 13.32/5.98  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.32/5.98  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 13.32/5.98  tff(c_16, plain, (![D_25, C_24, B_23, A_22]: (k2_enumset1(D_25, C_24, B_23, A_22)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.32/5.98  tff(c_346, plain, (![B_92, D_93, C_94, A_95]: (k2_enumset1(B_92, D_93, C_94, A_95)=k2_enumset1(A_95, B_92, C_94, D_93))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.32/5.98  tff(c_28, plain, (![A_48, B_49, C_50]: (k2_enumset1(A_48, A_48, B_49, C_50)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.32/5.98  tff(c_466, plain, (![B_96, D_97, C_98]: (k2_enumset1(B_96, D_97, C_98, B_96)=k1_enumset1(B_96, C_98, D_97))), inference(superposition, [status(thm), theory('equality')], [c_346, c_28])).
% 13.32/5.98  tff(c_918, plain, (![A_113, B_114, C_115]: (k2_enumset1(A_113, B_114, C_115, A_113)=k1_enumset1(A_113, B_114, C_115))), inference(superposition, [status(thm), theory('equality')], [c_16, c_466])).
% 13.32/5.98  tff(c_402, plain, (![B_92, D_93, C_94]: (k2_enumset1(B_92, D_93, C_94, B_92)=k1_enumset1(B_92, C_94, D_93))), inference(superposition, [status(thm), theory('equality')], [c_346, c_28])).
% 13.32/5.98  tff(c_934, plain, (![A_113, C_115, B_114]: (k1_enumset1(A_113, C_115, B_114)=k1_enumset1(A_113, B_114, C_115))), inference(superposition, [status(thm), theory('equality')], [c_918, c_402])).
% 13.32/5.98  tff(c_10, plain, (![A_10, C_12, B_11, D_13]: (k2_enumset1(A_10, C_12, B_11, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.32/5.98  tff(c_30, plain, (![A_51, B_52, C_53, D_54]: (k3_enumset1(A_51, A_51, B_52, C_53, D_54)=k2_enumset1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.32/5.98  tff(c_26, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.32/5.98  tff(c_32, plain, (![B_56, E_59, C_57, A_55, D_58]: (k4_enumset1(A_55, A_55, B_56, C_57, D_58, E_59)=k3_enumset1(A_55, B_56, C_57, D_58, E_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.32/5.98  tff(c_1592, plain, (![D_148, B_149, F_152, C_153, E_150, A_151]: (k2_xboole_0(k2_enumset1(A_151, B_149, C_153, D_148), k2_tarski(E_150, F_152))=k4_enumset1(A_151, B_149, C_153, D_148, E_150, F_152))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.32/5.98  tff(c_1649, plain, (![B_49, A_48, C_50, F_152, E_150]: (k4_enumset1(A_48, A_48, B_49, C_50, E_150, F_152)=k2_xboole_0(k1_enumset1(A_48, B_49, C_50), k2_tarski(E_150, F_152)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1592])).
% 13.32/5.98  tff(c_8153, plain, (![E_244, F_245, C_243, A_242, B_241]: (k2_xboole_0(k1_enumset1(A_242, B_241, C_243), k2_tarski(E_244, F_245))=k3_enumset1(A_242, B_241, C_243, E_244, F_245))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1649])).
% 13.32/5.98  tff(c_8177, plain, (![A_46, B_47, E_244, F_245]: (k3_enumset1(A_46, A_46, B_47, E_244, F_245)=k2_xboole_0(k2_tarski(A_46, B_47), k2_tarski(E_244, F_245)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8153])).
% 13.32/5.98  tff(c_8183, plain, (![A_46, B_47, E_244, F_245]: (k2_xboole_0(k2_tarski(A_46, B_47), k2_tarski(E_244, F_245))=k2_enumset1(A_46, B_47, E_244, F_245))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_8177])).
% 13.32/5.98  tff(c_82, plain, (![D_76, C_77, B_78, A_79]: (k2_enumset1(D_76, C_77, B_78, A_79)=k2_enumset1(A_79, B_78, C_77, D_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.32/5.98  tff(c_98, plain, (![D_76, C_77, B_78]: (k2_enumset1(D_76, C_77, B_78, B_78)=k1_enumset1(B_78, C_77, D_76))), inference(superposition, [status(thm), theory('equality')], [c_82, c_28])).
% 13.32/5.98  tff(c_1514, plain, (![C_140, D_137, A_139, B_138, E_141]: (k2_xboole_0(k2_enumset1(A_139, B_138, C_140, D_137), k1_tarski(E_141))=k3_enumset1(A_139, B_138, C_140, D_137, E_141))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.32/5.98  tff(c_1571, plain, (![A_48, B_49, C_50, E_141]: (k3_enumset1(A_48, A_48, B_49, C_50, E_141)=k2_xboole_0(k1_enumset1(A_48, B_49, C_50), k1_tarski(E_141)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1514])).
% 13.32/5.98  tff(c_1574, plain, (![A_48, B_49, C_50, E_141]: (k2_xboole_0(k1_enumset1(A_48, B_49, C_50), k1_tarski(E_141))=k2_enumset1(A_48, B_49, C_50, E_141))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1571])).
% 13.32/5.98  tff(c_24, plain, (![A_45]: (k2_tarski(A_45, A_45)=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.32/5.98  tff(c_8180, plain, (![A_242, B_241, C_243, A_45]: (k3_enumset1(A_242, B_241, C_243, A_45, A_45)=k2_xboole_0(k1_enumset1(A_242, B_241, C_243), k1_tarski(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8153])).
% 13.32/5.98  tff(c_10747, plain, (![A_324, B_325, C_326, A_327]: (k3_enumset1(A_324, B_325, C_326, A_327, A_327)=k2_enumset1(A_324, B_325, C_326, A_327))), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_8180])).
% 13.32/5.98  tff(c_10760, plain, (![B_325, C_326, A_327]: (k2_enumset1(B_325, C_326, A_327, A_327)=k2_enumset1(B_325, B_325, C_326, A_327))), inference(superposition, [status(thm), theory('equality')], [c_10747, c_30])).
% 13.32/5.98  tff(c_10780, plain, (![B_328, C_329, A_330]: (k1_enumset1(B_328, C_329, A_330)=k1_enumset1(A_330, C_329, B_328))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28, c_10760])).
% 13.32/5.98  tff(c_129, plain, (![D_80, C_81, B_82]: (k2_enumset1(D_80, C_81, B_82, B_82)=k1_enumset1(B_82, C_81, D_80))), inference(superposition, [status(thm), theory('equality')], [c_82, c_28])).
% 13.32/5.98  tff(c_142, plain, (![C_81, B_82]: (k1_enumset1(C_81, B_82, B_82)=k1_enumset1(B_82, C_81, C_81))), inference(superposition, [status(thm), theory('equality')], [c_129, c_28])).
% 13.32/5.98  tff(c_10820, plain, (![B_328, A_330]: (k1_enumset1(B_328, B_328, A_330)=k1_enumset1(B_328, A_330, A_330))), inference(superposition, [status(thm), theory('equality')], [c_10780, c_142])).
% 13.32/5.98  tff(c_10887, plain, (![B_328, A_330]: (k1_enumset1(B_328, A_330, A_330)=k2_tarski(B_328, A_330))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10820])).
% 13.32/5.98  tff(c_10899, plain, (![C_81, B_82]: (k2_tarski(C_81, B_82)=k2_tarski(B_82, C_81))), inference(demodulation, [status(thm), theory('equality')], [c_10887, c_10887, c_142])).
% 13.32/5.98  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.32/5.98  tff(c_1037, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_934, c_36])).
% 13.32/5.98  tff(c_10950, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10899, c_10899, c_1037])).
% 13.32/5.98  tff(c_26120, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8183, c_10950])).
% 13.32/5.98  tff(c_26123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_934, c_28, c_10, c_26120])).
% 13.32/5.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/5.98  
% 13.32/5.98  Inference rules
% 13.32/5.98  ----------------------
% 13.32/5.98  #Ref     : 0
% 13.32/5.98  #Sup     : 6516
% 13.32/5.98  #Fact    : 0
% 13.32/5.98  #Define  : 0
% 13.32/5.98  #Split   : 0
% 13.32/5.98  #Chain   : 0
% 13.32/5.98  #Close   : 0
% 13.32/5.98  
% 13.32/5.98  Ordering : KBO
% 13.32/5.98  
% 13.32/5.98  Simplification rules
% 13.32/5.98  ----------------------
% 13.32/5.98  #Subsume      : 2128
% 13.32/5.98  #Demod        : 5028
% 13.32/5.98  #Tautology    : 3018
% 13.32/5.98  #SimpNegUnit  : 0
% 13.32/5.98  #BackRed      : 4
% 13.32/5.98  
% 13.32/5.98  #Partial instantiations: 0
% 13.32/5.98  #Strategies tried      : 1
% 13.32/5.98  
% 13.32/5.98  Timing (in seconds)
% 13.32/5.98  ----------------------
% 13.32/5.98  Preprocessing        : 0.32
% 13.32/5.98  Parsing              : 0.17
% 13.32/5.98  CNF conversion       : 0.02
% 13.32/5.98  Main loop            : 4.83
% 13.32/5.98  Inferencing          : 0.88
% 13.32/5.98  Reduction            : 3.25
% 13.32/5.98  Demodulation         : 3.09
% 13.32/5.98  BG Simplification    : 0.10
% 13.32/5.98  Subsumption          : 0.46
% 13.32/5.98  Abstraction          : 0.17
% 13.32/5.98  MUC search           : 0.00
% 13.32/5.98  Cooper               : 0.00
% 13.32/5.98  Total                : 5.18
% 13.32/5.98  Index Insertion      : 0.00
% 13.32/5.98  Index Deletion       : 0.00
% 13.32/5.98  Index Matching       : 0.00
% 13.32/5.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
