%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:47 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   38 (  46 expanded)
%              Number of equality atoms :   33 (  41 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_enumset1(A_27,A_27,B_28,C_29,D_30,E_31) = k3_enumset1(A_27,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k5_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43,G_44) = k5_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_497,plain,(
    ! [A_106,H_104,C_101,G_105,B_100,F_99,D_102,E_103] : k2_xboole_0(k4_enumset1(A_106,B_100,C_101,D_102,E_103,F_99),k2_tarski(G_105,H_104)) = k6_enumset1(A_106,B_100,C_101,D_102,E_103,F_99,G_105,H_104) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_715,plain,(
    ! [B_111,H_113,C_114,A_116,G_112,D_115,F_109,E_110] : k4_xboole_0(k4_enumset1(A_116,B_111,C_114,D_115,E_110,F_109),k6_enumset1(A_116,B_111,C_114,D_115,E_110,F_109,G_112,H_113)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_8])).

tff(c_725,plain,(
    ! [D_41,B_39,A_38,F_43,G_44,E_42,C_40] : k4_xboole_0(k4_enumset1(A_38,A_38,B_39,C_40,D_41,E_42),k5_enumset1(A_38,B_39,C_40,D_41,E_42,F_43,G_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_715])).

tff(c_733,plain,(
    ! [E_119,B_118,F_120,A_117,D_123,C_122,G_121] : k4_xboole_0(k3_enumset1(A_117,B_118,C_122,D_123,E_119),k5_enumset1(A_117,B_118,C_122,D_123,E_119,F_120,G_121)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_725])).

tff(c_743,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k4_xboole_0(k3_enumset1(A_32,A_32,B_33,C_34,D_35),k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_733])).

tff(c_842,plain,(
    ! [B_132,D_136,C_134,E_131,F_133,A_135] : k4_xboole_0(k2_enumset1(A_135,B_132,C_134,D_136),k4_enumset1(A_135,B_132,C_134,D_136,E_131,F_133)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_743])).

tff(c_852,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] : k4_xboole_0(k2_enumset1(A_27,A_27,B_28,C_29),k3_enumset1(A_27,B_28,C_29,D_30,E_31)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_842])).

tff(c_860,plain,(
    ! [C_137,B_140,D_138,A_141,E_139] : k4_xboole_0(k1_enumset1(A_141,B_140,C_137),k3_enumset1(A_141,B_140,C_137,D_138,E_139)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_852])).

tff(c_870,plain,(
    ! [A_23,B_24,C_25,D_26] : k4_xboole_0(k1_enumset1(A_23,A_23,B_24),k2_enumset1(A_23,B_24,C_25,D_26)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_860])).

tff(c_878,plain,(
    ! [A_142,B_143,C_144,D_145] : k4_xboole_0(k2_tarski(A_142,B_143),k2_enumset1(A_142,B_143,C_144,D_145)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_870])).

tff(c_888,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k2_tarski(A_20,A_20),k1_enumset1(A_20,B_21,C_22)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_878])).

tff(c_896,plain,(
    ! [A_146,B_147,C_148] : k4_xboole_0(k1_tarski(A_146),k1_enumset1(A_146,B_147,C_148)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_888])).

tff(c_906,plain,(
    ! [A_18,B_19] : k4_xboole_0(k1_tarski(A_18),k2_tarski(A_18,B_19)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_896])).

tff(c_55,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | k4_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_28])).

tff(c_911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.34/1.52  
% 3.34/1.52  %Foreground sorts:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Background operators:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Foreground operators:
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.52  
% 3.44/1.53  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.44/1.53  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.53  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.44/1.53  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.44/1.53  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.44/1.53  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.44/1.53  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.44/1.53  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 3.44/1.53  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.44/1.53  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.44/1.53  tff(f_54, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.44/1.53  tff(c_16, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.53  tff(c_14, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.53  tff(c_18, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.53  tff(c_20, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.53  tff(c_22, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_enumset1(A_27, A_27, B_28, C_29, D_30, E_31)=k3_enumset1(A_27, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.53  tff(c_24, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k5_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37)=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.53  tff(c_26, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43, G_44)=k5_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.53  tff(c_497, plain, (![A_106, H_104, C_101, G_105, B_100, F_99, D_102, E_103]: (k2_xboole_0(k4_enumset1(A_106, B_100, C_101, D_102, E_103, F_99), k2_tarski(G_105, H_104))=k6_enumset1(A_106, B_100, C_101, D_102, E_103, F_99, G_105, H_104))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.53  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.53  tff(c_715, plain, (![B_111, H_113, C_114, A_116, G_112, D_115, F_109, E_110]: (k4_xboole_0(k4_enumset1(A_116, B_111, C_114, D_115, E_110, F_109), k6_enumset1(A_116, B_111, C_114, D_115, E_110, F_109, G_112, H_113))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_497, c_8])).
% 3.44/1.53  tff(c_725, plain, (![D_41, B_39, A_38, F_43, G_44, E_42, C_40]: (k4_xboole_0(k4_enumset1(A_38, A_38, B_39, C_40, D_41, E_42), k5_enumset1(A_38, B_39, C_40, D_41, E_42, F_43, G_44))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_715])).
% 3.44/1.53  tff(c_733, plain, (![E_119, B_118, F_120, A_117, D_123, C_122, G_121]: (k4_xboole_0(k3_enumset1(A_117, B_118, C_122, D_123, E_119), k5_enumset1(A_117, B_118, C_122, D_123, E_119, F_120, G_121))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_725])).
% 3.44/1.53  tff(c_743, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k4_xboole_0(k3_enumset1(A_32, A_32, B_33, C_34, D_35), k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_733])).
% 3.44/1.53  tff(c_842, plain, (![B_132, D_136, C_134, E_131, F_133, A_135]: (k4_xboole_0(k2_enumset1(A_135, B_132, C_134, D_136), k4_enumset1(A_135, B_132, C_134, D_136, E_131, F_133))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_743])).
% 3.44/1.53  tff(c_852, plain, (![C_29, D_30, B_28, A_27, E_31]: (k4_xboole_0(k2_enumset1(A_27, A_27, B_28, C_29), k3_enumset1(A_27, B_28, C_29, D_30, E_31))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_842])).
% 3.44/1.53  tff(c_860, plain, (![C_137, B_140, D_138, A_141, E_139]: (k4_xboole_0(k1_enumset1(A_141, B_140, C_137), k3_enumset1(A_141, B_140, C_137, D_138, E_139))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_852])).
% 3.44/1.53  tff(c_870, plain, (![A_23, B_24, C_25, D_26]: (k4_xboole_0(k1_enumset1(A_23, A_23, B_24), k2_enumset1(A_23, B_24, C_25, D_26))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_860])).
% 3.44/1.53  tff(c_878, plain, (![A_142, B_143, C_144, D_145]: (k4_xboole_0(k2_tarski(A_142, B_143), k2_enumset1(A_142, B_143, C_144, D_145))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_870])).
% 3.44/1.53  tff(c_888, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k2_tarski(A_20, A_20), k1_enumset1(A_20, B_21, C_22))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_878])).
% 3.44/1.53  tff(c_896, plain, (![A_146, B_147, C_148]: (k4_xboole_0(k1_tarski(A_146), k1_enumset1(A_146, B_147, C_148))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_888])).
% 3.44/1.53  tff(c_906, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), k2_tarski(A_18, B_19))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_896])).
% 3.44/1.53  tff(c_55, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | k4_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.53  tff(c_28, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.53  tff(c_63, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_55, c_28])).
% 3.44/1.53  tff(c_911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_906, c_63])).
% 3.44/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.53  
% 3.44/1.53  Inference rules
% 3.44/1.53  ----------------------
% 3.44/1.53  #Ref     : 0
% 3.44/1.53  #Sup     : 230
% 3.44/1.53  #Fact    : 0
% 3.44/1.53  #Define  : 0
% 3.44/1.53  #Split   : 0
% 3.44/1.53  #Chain   : 0
% 3.44/1.53  #Close   : 0
% 3.44/1.53  
% 3.44/1.53  Ordering : KBO
% 3.44/1.53  
% 3.44/1.53  Simplification rules
% 3.44/1.53  ----------------------
% 3.44/1.53  #Subsume      : 3
% 3.44/1.53  #Demod        : 182
% 3.44/1.53  #Tautology    : 85
% 3.44/1.53  #SimpNegUnit  : 0
% 3.44/1.53  #BackRed      : 1
% 3.44/1.53  
% 3.44/1.53  #Partial instantiations: 0
% 3.44/1.53  #Strategies tried      : 1
% 3.44/1.53  
% 3.44/1.53  Timing (in seconds)
% 3.44/1.53  ----------------------
% 3.44/1.54  Preprocessing        : 0.31
% 3.44/1.54  Parsing              : 0.17
% 3.44/1.54  CNF conversion       : 0.02
% 3.44/1.54  Main loop            : 0.45
% 3.44/1.54  Inferencing          : 0.15
% 3.44/1.54  Reduction            : 0.21
% 3.44/1.54  Demodulation         : 0.18
% 3.44/1.54  BG Simplification    : 0.03
% 3.44/1.54  Subsumption          : 0.04
% 3.44/1.54  Abstraction          : 0.04
% 3.44/1.54  MUC search           : 0.00
% 3.44/1.54  Cooper               : 0.00
% 3.44/1.54  Total                : 0.80
% 3.44/1.54  Index Insertion      : 0.00
% 3.44/1.54  Index Deletion       : 0.00
% 3.44/1.54  Index Matching       : 0.00
% 3.44/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
