%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   28 (  59 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :   10 (   5 average)
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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_36,B_37,C_38,D_39] : k3_enumset1(A_36,A_36,B_37,C_38,D_39) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [E_44,C_42,A_40,D_43,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,E_44) = k3_enumset1(A_40,B_41,C_42,D_43,E_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_48,C_47,A_45,B_46,E_49,F_50] : k5_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,F_50) = k4_enumset1(A_45,B_46,C_47,D_48,E_49,F_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143,plain,(
    ! [D_92,F_97,A_95,G_96,C_94,E_98,B_93] : k2_xboole_0(k4_enumset1(A_95,B_93,C_94,D_92,E_98,F_97),k1_tarski(G_96)) = k5_enumset1(A_95,B_93,C_94,D_92,E_98,F_97,G_96) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [E_44,C_42,G_96,A_40,D_43,B_41] : k5_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,G_96) = k2_xboole_0(k3_enumset1(A_40,B_41,C_42,D_43,E_44),k1_tarski(G_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_156,plain,(
    ! [G_103,B_104,E_99,C_102,A_100,D_101] : k2_xboole_0(k3_enumset1(A_100,B_104,C_102,D_101,E_99),k1_tarski(G_103)) = k4_enumset1(A_100,B_104,C_102,D_101,E_99,G_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_152])).

tff(c_165,plain,(
    ! [G_103,D_39,A_36,C_38,B_37] : k4_enumset1(A_36,A_36,B_37,C_38,D_39,G_103) = k2_xboole_0(k2_enumset1(A_36,B_37,C_38,D_39),k1_tarski(G_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_156])).

tff(c_169,plain,(
    ! [A_105,G_106,B_108,C_109,D_107] : k2_xboole_0(k2_enumset1(A_105,B_108,C_109,D_107),k1_tarski(G_106)) = k3_enumset1(A_105,B_108,C_109,D_107,G_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_165])).

tff(c_178,plain,(
    ! [A_33,B_34,C_35,G_106] : k3_enumset1(A_33,A_33,B_34,C_35,G_106) = k2_xboole_0(k1_enumset1(A_33,B_34,C_35),k1_tarski(G_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_169])).

tff(c_182,plain,(
    ! [A_110,B_111,C_112,G_113] : k2_xboole_0(k1_enumset1(A_110,B_111,C_112),k1_tarski(G_113)) = k2_enumset1(A_110,B_111,C_112,G_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_178])).

tff(c_191,plain,(
    ! [A_31,B_32,G_113] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(G_113)) = k2_enumset1(A_31,A_31,B_32,G_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_182])).

tff(c_217,plain,(
    ! [A_122,B_123,G_124] : k2_xboole_0(k2_tarski(A_122,B_123),k1_tarski(G_124)) = k1_enumset1(A_122,B_123,G_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_191])).

tff(c_245,plain,(
    ! [B_127,A_128,G_129] : k2_xboole_0(k2_tarski(B_127,A_128),k1_tarski(G_129)) = k1_enumset1(A_128,B_127,G_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_217])).

tff(c_194,plain,(
    ! [A_31,B_32,G_113] : k2_xboole_0(k2_tarski(A_31,B_32),k1_tarski(G_113)) = k1_enumset1(A_31,B_32,G_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_191])).

tff(c_251,plain,(
    ! [B_127,A_128,G_129] : k1_enumset1(B_127,A_128,G_129) = k1_enumset1(A_128,B_127,G_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_194])).

tff(c_28,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.96/1.23  
% 1.96/1.23  %Foreground sorts:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Background operators:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Foreground operators:
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.23  
% 2.17/1.24  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.24  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.17/1.24  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.24  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.17/1.24  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.17/1.24  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.17/1.24  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.17/1.24  tff(f_54, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 2.17/1.24  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.24  tff(c_18, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.24  tff(c_16, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.24  tff(c_20, plain, (![A_36, B_37, C_38, D_39]: (k3_enumset1(A_36, A_36, B_37, C_38, D_39)=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.24  tff(c_22, plain, (![E_44, C_42, A_40, D_43, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, E_44)=k3_enumset1(A_40, B_41, C_42, D_43, E_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.24  tff(c_24, plain, (![D_48, C_47, A_45, B_46, E_49, F_50]: (k5_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, F_50)=k4_enumset1(A_45, B_46, C_47, D_48, E_49, F_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.24  tff(c_143, plain, (![D_92, F_97, A_95, G_96, C_94, E_98, B_93]: (k2_xboole_0(k4_enumset1(A_95, B_93, C_94, D_92, E_98, F_97), k1_tarski(G_96))=k5_enumset1(A_95, B_93, C_94, D_92, E_98, F_97, G_96))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.24  tff(c_152, plain, (![E_44, C_42, G_96, A_40, D_43, B_41]: (k5_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, G_96)=k2_xboole_0(k3_enumset1(A_40, B_41, C_42, D_43, E_44), k1_tarski(G_96)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_143])).
% 2.17/1.24  tff(c_156, plain, (![G_103, B_104, E_99, C_102, A_100, D_101]: (k2_xboole_0(k3_enumset1(A_100, B_104, C_102, D_101, E_99), k1_tarski(G_103))=k4_enumset1(A_100, B_104, C_102, D_101, E_99, G_103))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_152])).
% 2.17/1.24  tff(c_165, plain, (![G_103, D_39, A_36, C_38, B_37]: (k4_enumset1(A_36, A_36, B_37, C_38, D_39, G_103)=k2_xboole_0(k2_enumset1(A_36, B_37, C_38, D_39), k1_tarski(G_103)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_156])).
% 2.17/1.24  tff(c_169, plain, (![A_105, G_106, B_108, C_109, D_107]: (k2_xboole_0(k2_enumset1(A_105, B_108, C_109, D_107), k1_tarski(G_106))=k3_enumset1(A_105, B_108, C_109, D_107, G_106))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_165])).
% 2.17/1.24  tff(c_178, plain, (![A_33, B_34, C_35, G_106]: (k3_enumset1(A_33, A_33, B_34, C_35, G_106)=k2_xboole_0(k1_enumset1(A_33, B_34, C_35), k1_tarski(G_106)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_169])).
% 2.17/1.24  tff(c_182, plain, (![A_110, B_111, C_112, G_113]: (k2_xboole_0(k1_enumset1(A_110, B_111, C_112), k1_tarski(G_113))=k2_enumset1(A_110, B_111, C_112, G_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_178])).
% 2.17/1.24  tff(c_191, plain, (![A_31, B_32, G_113]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(G_113))=k2_enumset1(A_31, A_31, B_32, G_113))), inference(superposition, [status(thm), theory('equality')], [c_16, c_182])).
% 2.17/1.24  tff(c_217, plain, (![A_122, B_123, G_124]: (k2_xboole_0(k2_tarski(A_122, B_123), k1_tarski(G_124))=k1_enumset1(A_122, B_123, G_124))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_191])).
% 2.17/1.24  tff(c_245, plain, (![B_127, A_128, G_129]: (k2_xboole_0(k2_tarski(B_127, A_128), k1_tarski(G_129))=k1_enumset1(A_128, B_127, G_129))), inference(superposition, [status(thm), theory('equality')], [c_6, c_217])).
% 2.17/1.24  tff(c_194, plain, (![A_31, B_32, G_113]: (k2_xboole_0(k2_tarski(A_31, B_32), k1_tarski(G_113))=k1_enumset1(A_31, B_32, G_113))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_191])).
% 2.17/1.24  tff(c_251, plain, (![B_127, A_128, G_129]: (k1_enumset1(B_127, A_128, G_129)=k1_enumset1(A_128, B_127, G_129))), inference(superposition, [status(thm), theory('equality')], [c_245, c_194])).
% 2.17/1.24  tff(c_28, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.24  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_28])).
% 2.17/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  Inference rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Ref     : 0
% 2.17/1.24  #Sup     : 64
% 2.17/1.24  #Fact    : 0
% 2.17/1.24  #Define  : 0
% 2.17/1.24  #Split   : 0
% 2.17/1.24  #Chain   : 0
% 2.17/1.24  #Close   : 0
% 2.17/1.24  
% 2.17/1.24  Ordering : KBO
% 2.17/1.24  
% 2.17/1.24  Simplification rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Subsume      : 0
% 2.17/1.24  #Demod        : 13
% 2.17/1.24  #Tautology    : 47
% 2.17/1.24  #SimpNegUnit  : 0
% 2.17/1.24  #BackRed      : 1
% 2.17/1.24  
% 2.17/1.24  #Partial instantiations: 0
% 2.17/1.24  #Strategies tried      : 1
% 2.17/1.24  
% 2.17/1.25  Timing (in seconds)
% 2.17/1.25  ----------------------
% 2.17/1.25  Preprocessing        : 0.31
% 2.17/1.25  Parsing              : 0.17
% 2.17/1.25  CNF conversion       : 0.02
% 2.17/1.25  Main loop            : 0.18
% 2.17/1.25  Inferencing          : 0.08
% 2.17/1.25  Reduction            : 0.06
% 2.17/1.25  Demodulation         : 0.05
% 2.17/1.25  BG Simplification    : 0.02
% 2.17/1.25  Subsumption          : 0.02
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.52
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
