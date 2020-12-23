%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:14 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   38 (  72 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  52 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k2_tarski(A,B),k5_enumset1(C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k2_tarski(H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [B_78,H_79,C_84,E_81,I_85,G_77,A_80,D_82,F_83] : k2_xboole_0(k2_tarski(A_80,B_78),k5_enumset1(C_84,D_82,E_81,F_83,G_77,H_79,I_85)) = k7_enumset1(A_80,B_78,C_84,D_82,E_81,F_83,G_77,H_79,I_85) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_95,H_102,D_96,F_101,I_99,B_97,G_98,C_100,E_103] : k2_xboole_0(k5_enumset1(C_100,D_96,E_103,F_101,G_98,H_102,I_99),k2_tarski(A_95,B_97)) = k7_enumset1(A_95,B_97,C_100,D_96,E_103,F_101,G_98,H_102,I_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_12,plain,(
    ! [E_43,H_46,G_45,F_44,D_42,A_39,C_41,B_40,I_47] : k2_xboole_0(k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45),k2_tarski(H_46,I_47)) = k7_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45,H_46,I_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [A_95,H_102,D_96,F_101,I_99,B_97,G_98,C_100,E_103] : k7_enumset1(C_100,D_96,E_103,F_101,G_98,H_102,I_99,A_95,B_97) = k7_enumset1(A_95,B_97,C_100,D_96,E_103,F_101,G_98,H_102,I_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_12])).

tff(c_187,plain,(
    ! [E_108,I_109,A_110,D_112,H_107,C_106,B_105,F_111,G_104] : k7_enumset1(C_106,D_112,E_108,F_111,G_104,H_107,I_109,A_110,B_105) = k7_enumset1(A_110,B_105,C_106,D_112,E_108,F_111,G_104,H_107,I_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_12])).

tff(c_202,plain,(
    ! [A_95,H_102,D_96,F_101,I_99,B_97,G_98,C_100,E_103] : k7_enumset1(H_102,I_99,A_95,B_97,C_100,D_96,E_103,F_101,G_98) = k7_enumset1(C_100,D_96,E_103,F_101,G_98,H_102,I_99,A_95,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_187])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,I_11,C_5,H_10,G_9,E_7,B_4] : k2_xboole_0(k1_tarski(A_3),k6_enumset1(B_4,C_5,D_6,E_7,F_8,G_9,H_10,I_11)) = k7_enumset1(A_3,B_4,C_5,D_6,E_7,F_8,G_9,H_10,I_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    k2_xboole_0(k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8'),k1_tarski('#skF_9')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0(k1_tarski('#skF_9'),k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_16,plain,(
    k7_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k7_enumset1('#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_15])).

tff(c_186,plain,(
    k7_enumset1('#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') != k7_enumset1('#skF_8','#skF_9','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_16])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_202,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.22  
% 2.15/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.22  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.15/1.22  
% 2.15/1.22  %Foreground sorts:
% 2.15/1.22  
% 2.15/1.22  
% 2.15/1.22  %Background operators:
% 2.15/1.22  
% 2.15/1.22  
% 2.15/1.22  %Foreground operators:
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.22  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.22  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.22  tff('#skF_9', type, '#skF_9': $i).
% 2.15/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.22  tff('#skF_8', type, '#skF_8': $i).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.22  
% 2.15/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.15/1.23  tff(f_31, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k2_tarski(A, B), k5_enumset1(C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_enumset1)).
% 2.15/1.23  tff(f_37, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k2_tarski(H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_enumset1)).
% 2.15/1.23  tff(f_29, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 2.15/1.23  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 2.15/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.23  tff(c_113, plain, (![B_78, H_79, C_84, E_81, I_85, G_77, A_80, D_82, F_83]: (k2_xboole_0(k2_tarski(A_80, B_78), k5_enumset1(C_84, D_82, E_81, F_83, G_77, H_79, I_85))=k7_enumset1(A_80, B_78, C_84, D_82, E_81, F_83, G_77, H_79, I_85))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.23  tff(c_155, plain, (![A_95, H_102, D_96, F_101, I_99, B_97, G_98, C_100, E_103]: (k2_xboole_0(k5_enumset1(C_100, D_96, E_103, F_101, G_98, H_102, I_99), k2_tarski(A_95, B_97))=k7_enumset1(A_95, B_97, C_100, D_96, E_103, F_101, G_98, H_102, I_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 2.15/1.23  tff(c_12, plain, (![E_43, H_46, G_45, F_44, D_42, A_39, C_41, B_40, I_47]: (k2_xboole_0(k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45), k2_tarski(H_46, I_47))=k7_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45, H_46, I_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.23  tff(c_161, plain, (![A_95, H_102, D_96, F_101, I_99, B_97, G_98, C_100, E_103]: (k7_enumset1(C_100, D_96, E_103, F_101, G_98, H_102, I_99, A_95, B_97)=k7_enumset1(A_95, B_97, C_100, D_96, E_103, F_101, G_98, H_102, I_99))), inference(superposition, [status(thm), theory('equality')], [c_155, c_12])).
% 2.15/1.23  tff(c_187, plain, (![E_108, I_109, A_110, D_112, H_107, C_106, B_105, F_111, G_104]: (k7_enumset1(C_106, D_112, E_108, F_111, G_104, H_107, I_109, A_110, B_105)=k7_enumset1(A_110, B_105, C_106, D_112, E_108, F_111, G_104, H_107, I_109))), inference(superposition, [status(thm), theory('equality')], [c_155, c_12])).
% 2.15/1.23  tff(c_202, plain, (![A_95, H_102, D_96, F_101, I_99, B_97, G_98, C_100, E_103]: (k7_enumset1(H_102, I_99, A_95, B_97, C_100, D_96, E_103, F_101, G_98)=k7_enumset1(C_100, D_96, E_103, F_101, G_98, H_102, I_99, A_95, B_97))), inference(superposition, [status(thm), theory('equality')], [c_161, c_187])).
% 2.15/1.23  tff(c_4, plain, (![A_3, F_8, D_6, I_11, C_5, H_10, G_9, E_7, B_4]: (k2_xboole_0(k1_tarski(A_3), k6_enumset1(B_4, C_5, D_6, E_7, F_8, G_9, H_10, I_11))=k7_enumset1(A_3, B_4, C_5, D_6, E_7, F_8, G_9, H_10, I_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.23  tff(c_14, plain, (k2_xboole_0(k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'), k1_tarski('#skF_9'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.23  tff(c_15, plain, (k2_xboole_0(k1_tarski('#skF_9'), k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 2.15/1.23  tff(c_16, plain, (k7_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k7_enumset1('#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_15])).
% 2.15/1.23  tff(c_186, plain, (k7_enumset1('#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')!=k7_enumset1('#skF_8', '#skF_9', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_16])).
% 2.15/1.23  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_202, c_186])).
% 2.15/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  Inference rules
% 2.29/1.23  ----------------------
% 2.29/1.23  #Ref     : 0
% 2.29/1.23  #Sup     : 54
% 2.29/1.23  #Fact    : 0
% 2.29/1.23  #Define  : 0
% 2.29/1.23  #Split   : 0
% 2.29/1.23  #Chain   : 0
% 2.29/1.23  #Close   : 0
% 2.29/1.23  
% 2.29/1.23  Ordering : KBO
% 2.29/1.23  
% 2.29/1.23  Simplification rules
% 2.29/1.23  ----------------------
% 2.29/1.23  #Subsume      : 1
% 2.29/1.23  #Demod        : 9
% 2.29/1.23  #Tautology    : 28
% 2.29/1.23  #SimpNegUnit  : 0
% 2.29/1.23  #BackRed      : 2
% 2.29/1.23  
% 2.29/1.23  #Partial instantiations: 0
% 2.29/1.23  #Strategies tried      : 1
% 2.29/1.23  
% 2.29/1.23  Timing (in seconds)
% 2.29/1.23  ----------------------
% 2.29/1.24  Preprocessing        : 0.29
% 2.29/1.24  Parsing              : 0.15
% 2.29/1.24  CNF conversion       : 0.02
% 2.29/1.24  Main loop            : 0.19
% 2.29/1.24  Inferencing          : 0.08
% 2.29/1.24  Reduction            : 0.07
% 2.29/1.24  Demodulation         : 0.06
% 2.29/1.24  BG Simplification    : 0.02
% 2.29/1.24  Subsumption          : 0.03
% 2.29/1.24  Abstraction          : 0.01
% 2.29/1.24  MUC search           : 0.00
% 2.29/1.24  Cooper               : 0.00
% 2.29/1.24  Total                : 0.51
% 2.29/1.24  Index Insertion      : 0.00
% 2.29/1.24  Index Deletion       : 0.00
% 2.29/1.24  Index Matching       : 0.00
% 2.29/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
