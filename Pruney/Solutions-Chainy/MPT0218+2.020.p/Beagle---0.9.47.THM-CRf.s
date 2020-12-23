%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_10,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22,D_23] : k3_enumset1(A_20,A_20,B_21,C_22,D_23) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] : k4_enumset1(A_24,A_24,B_25,C_26,D_27,E_28) = k3_enumset1(A_24,B_25,C_26,D_27,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] : k5_enumset1(A_29,A_29,B_30,C_31,D_32,E_33,F_34) = k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [B_77,C_78,G_80,F_81,E_82,A_79,D_76] : k2_xboole_0(k4_enumset1(A_79,B_77,C_78,D_76,E_82,F_81),k1_tarski(G_80)) = k5_enumset1(A_79,B_77,C_78,D_76,E_82,F_81,G_80) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [A_85,G_83,F_86,B_84,D_87,E_89,C_88] : r1_tarski(k4_enumset1(A_85,B_84,C_88,D_87,E_89,F_86),k5_enumset1(A_85,B_84,C_88,D_87,E_89,F_86,G_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_126,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] : r1_tarski(k4_enumset1(A_29,A_29,B_30,C_31,D_32,E_33),k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_132,plain,(
    ! [E_94,C_95,A_92,B_91,F_93,D_90] : r1_tarski(k3_enumset1(A_92,B_91,C_95,D_90,E_94),k4_enumset1(A_92,B_91,C_95,D_90,E_94,F_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_126])).

tff(c_135,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] : r1_tarski(k3_enumset1(A_24,A_24,B_25,C_26,D_27),k3_enumset1(A_24,B_25,C_26,D_27,E_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_132])).

tff(c_141,plain,(
    ! [C_96,A_99,D_100,E_98,B_97] : r1_tarski(k2_enumset1(A_99,B_97,C_96,D_100),k3_enumset1(A_99,B_97,C_96,D_100,E_98)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_135])).

tff(c_144,plain,(
    ! [A_20,B_21,C_22,D_23] : r1_tarski(k2_enumset1(A_20,A_20,B_21,C_22),k2_enumset1(A_20,B_21,C_22,D_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_141])).

tff(c_167,plain,(
    ! [A_107,B_108,C_109,D_110] : r1_tarski(k1_enumset1(A_107,B_108,C_109),k2_enumset1(A_107,B_108,C_109,D_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_170,plain,(
    ! [A_17,B_18,C_19] : r1_tarski(k1_enumset1(A_17,A_17,B_18),k1_enumset1(A_17,B_18,C_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_167])).

tff(c_176,plain,(
    ! [A_111,B_112,C_113] : r1_tarski(k2_tarski(A_111,B_112),k1_enumset1(A_111,B_112,C_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_170])).

tff(c_179,plain,(
    ! [A_15,B_16] : r1_tarski(k2_tarski(A_15,A_15),k2_tarski(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_183,plain,(
    ! [A_15,B_16] : r1_tarski(k1_tarski(A_15),k2_tarski(A_15,B_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_179])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.24  
% 2.07/1.25  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.25  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.07/1.25  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.07/1.25  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.07/1.25  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.07/1.25  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.07/1.25  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.07/1.25  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.25  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.07/1.25  tff(c_10, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.25  tff(c_12, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.25  tff(c_14, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.25  tff(c_16, plain, (![A_20, B_21, C_22, D_23]: (k3_enumset1(A_20, A_20, B_21, C_22, D_23)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.25  tff(c_18, plain, (![A_24, B_25, D_27, C_26, E_28]: (k4_enumset1(A_24, A_24, B_25, C_26, D_27, E_28)=k3_enumset1(A_24, B_25, C_26, D_27, E_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.25  tff(c_20, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (k5_enumset1(A_29, A_29, B_30, C_31, D_32, E_33, F_34)=k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.07/1.25  tff(c_107, plain, (![B_77, C_78, G_80, F_81, E_82, A_79, D_76]: (k2_xboole_0(k4_enumset1(A_79, B_77, C_78, D_76, E_82, F_81), k1_tarski(G_80))=k5_enumset1(A_79, B_77, C_78, D_76, E_82, F_81, G_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.25  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.25  tff(c_123, plain, (![A_85, G_83, F_86, B_84, D_87, E_89, C_88]: (r1_tarski(k4_enumset1(A_85, B_84, C_88, D_87, E_89, F_86), k5_enumset1(A_85, B_84, C_88, D_87, E_89, F_86, G_83)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 2.07/1.25  tff(c_126, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (r1_tarski(k4_enumset1(A_29, A_29, B_30, C_31, D_32, E_33), k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_123])).
% 2.07/1.25  tff(c_132, plain, (![E_94, C_95, A_92, B_91, F_93, D_90]: (r1_tarski(k3_enumset1(A_92, B_91, C_95, D_90, E_94), k4_enumset1(A_92, B_91, C_95, D_90, E_94, F_93)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_126])).
% 2.07/1.25  tff(c_135, plain, (![A_24, B_25, D_27, C_26, E_28]: (r1_tarski(k3_enumset1(A_24, A_24, B_25, C_26, D_27), k3_enumset1(A_24, B_25, C_26, D_27, E_28)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_132])).
% 2.07/1.25  tff(c_141, plain, (![C_96, A_99, D_100, E_98, B_97]: (r1_tarski(k2_enumset1(A_99, B_97, C_96, D_100), k3_enumset1(A_99, B_97, C_96, D_100, E_98)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_135])).
% 2.07/1.25  tff(c_144, plain, (![A_20, B_21, C_22, D_23]: (r1_tarski(k2_enumset1(A_20, A_20, B_21, C_22), k2_enumset1(A_20, B_21, C_22, D_23)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_141])).
% 2.07/1.25  tff(c_167, plain, (![A_107, B_108, C_109, D_110]: (r1_tarski(k1_enumset1(A_107, B_108, C_109), k2_enumset1(A_107, B_108, C_109, D_110)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_144])).
% 2.07/1.25  tff(c_170, plain, (![A_17, B_18, C_19]: (r1_tarski(k1_enumset1(A_17, A_17, B_18), k1_enumset1(A_17, B_18, C_19)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_167])).
% 2.07/1.25  tff(c_176, plain, (![A_111, B_112, C_113]: (r1_tarski(k2_tarski(A_111, B_112), k1_enumset1(A_111, B_112, C_113)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_170])).
% 2.07/1.25  tff(c_179, plain, (![A_15, B_16]: (r1_tarski(k2_tarski(A_15, A_15), k2_tarski(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_176])).
% 2.07/1.25  tff(c_183, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), k2_tarski(A_15, B_16)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_179])).
% 2.07/1.25  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.25  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_24])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 36
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 0
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 0
% 2.07/1.25  #Demod        : 14
% 2.07/1.25  #Tautology    : 23
% 2.07/1.25  #SimpNegUnit  : 0
% 2.07/1.25  #BackRed      : 1
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.31
% 2.07/1.25  Parsing              : 0.17
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.14
% 2.07/1.25  Inferencing          : 0.06
% 2.07/1.26  Reduction            : 0.05
% 2.07/1.26  Demodulation         : 0.04
% 2.07/1.26  BG Simplification    : 0.01
% 2.07/1.26  Subsumption          : 0.01
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.48
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
