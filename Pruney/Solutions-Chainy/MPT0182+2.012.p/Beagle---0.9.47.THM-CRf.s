%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:43 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   24 (  47 expanded)
%              Number of equality atoms :   23 (  46 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_31,B_32,C_33] : k2_enumset1(A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_34,B_35,C_36,D_37] : k3_enumset1(A_34,A_34,B_35,C_36,D_37) = k2_enumset1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [D_41,B_39,A_38,E_42,C_40] : k4_enumset1(A_38,A_38,B_39,C_40,D_41,E_42) = k3_enumset1(A_38,B_39,C_40,D_41,E_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [C_85,E_88,B_84,F_87,D_83,A_86] : k2_xboole_0(k3_enumset1(A_86,B_84,C_85,D_83,E_88),k1_tarski(F_87)) = k4_enumset1(A_86,B_84,C_85,D_83,E_88,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [D_37,A_34,B_35,F_87,C_36] : k4_enumset1(A_34,A_34,B_35,C_36,D_37,F_87) = k2_xboole_0(k2_enumset1(A_34,B_35,C_36,D_37),k1_tarski(F_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_134])).

tff(c_147,plain,(
    ! [F_92,A_89,B_91,C_93,D_90] : k2_xboole_0(k2_enumset1(A_89,B_91,C_93,D_90),k1_tarski(F_92)) = k3_enumset1(A_89,B_91,C_93,D_90,F_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_143])).

tff(c_156,plain,(
    ! [A_31,B_32,C_33,F_92] : k3_enumset1(A_31,A_31,B_32,C_33,F_92) = k2_xboole_0(k1_enumset1(A_31,B_32,C_33),k1_tarski(F_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_147])).

tff(c_160,plain,(
    ! [A_94,B_95,C_96,F_97] : k2_xboole_0(k1_enumset1(A_94,B_95,C_96),k1_tarski(F_97)) = k2_enumset1(A_94,B_95,C_96,F_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_156])).

tff(c_169,plain,(
    ! [A_29,B_30,F_97] : k2_xboole_0(k2_tarski(A_29,B_30),k1_tarski(F_97)) = k2_enumset1(A_29,A_29,B_30,F_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_160])).

tff(c_173,plain,(
    ! [A_98,B_99,F_100] : k2_xboole_0(k2_tarski(A_98,B_99),k1_tarski(F_100)) = k1_enumset1(A_98,B_99,F_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_169])).

tff(c_210,plain,(
    ! [A_110,B_111,F_112] : k2_xboole_0(k2_tarski(A_110,B_111),k1_tarski(F_112)) = k1_enumset1(B_111,A_110,F_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_173])).

tff(c_172,plain,(
    ! [A_29,B_30,F_97] : k2_xboole_0(k2_tarski(A_29,B_30),k1_tarski(F_97)) = k1_enumset1(A_29,B_30,F_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_169])).

tff(c_216,plain,(
    ! [B_111,A_110,F_112] : k1_enumset1(B_111,A_110,F_112) = k1_enumset1(A_110,B_111,F_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_172])).

tff(c_28,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:11:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.89/1.18  
% 1.89/1.18  %Foreground sorts:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Background operators:
% 1.89/1.18  
% 1.89/1.18  
% 1.89/1.18  %Foreground operators:
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.89/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.18  
% 1.98/1.19  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.98/1.19  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.98/1.19  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.98/1.19  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.98/1.19  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.98/1.19  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 1.98/1.19  tff(f_54, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.98/1.19  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.19  tff(c_18, plain, (![A_31, B_32, C_33]: (k2_enumset1(A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.98/1.19  tff(c_16, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.19  tff(c_20, plain, (![A_34, B_35, C_36, D_37]: (k3_enumset1(A_34, A_34, B_35, C_36, D_37)=k2_enumset1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.19  tff(c_22, plain, (![D_41, B_39, A_38, E_42, C_40]: (k4_enumset1(A_38, A_38, B_39, C_40, D_41, E_42)=k3_enumset1(A_38, B_39, C_40, D_41, E_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.19  tff(c_134, plain, (![C_85, E_88, B_84, F_87, D_83, A_86]: (k2_xboole_0(k3_enumset1(A_86, B_84, C_85, D_83, E_88), k1_tarski(F_87))=k4_enumset1(A_86, B_84, C_85, D_83, E_88, F_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.19  tff(c_143, plain, (![D_37, A_34, B_35, F_87, C_36]: (k4_enumset1(A_34, A_34, B_35, C_36, D_37, F_87)=k2_xboole_0(k2_enumset1(A_34, B_35, C_36, D_37), k1_tarski(F_87)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_134])).
% 1.98/1.19  tff(c_147, plain, (![F_92, A_89, B_91, C_93, D_90]: (k2_xboole_0(k2_enumset1(A_89, B_91, C_93, D_90), k1_tarski(F_92))=k3_enumset1(A_89, B_91, C_93, D_90, F_92))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_143])).
% 1.98/1.19  tff(c_156, plain, (![A_31, B_32, C_33, F_92]: (k3_enumset1(A_31, A_31, B_32, C_33, F_92)=k2_xboole_0(k1_enumset1(A_31, B_32, C_33), k1_tarski(F_92)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_147])).
% 1.98/1.19  tff(c_160, plain, (![A_94, B_95, C_96, F_97]: (k2_xboole_0(k1_enumset1(A_94, B_95, C_96), k1_tarski(F_97))=k2_enumset1(A_94, B_95, C_96, F_97))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_156])).
% 1.98/1.19  tff(c_169, plain, (![A_29, B_30, F_97]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_tarski(F_97))=k2_enumset1(A_29, A_29, B_30, F_97))), inference(superposition, [status(thm), theory('equality')], [c_16, c_160])).
% 1.98/1.19  tff(c_173, plain, (![A_98, B_99, F_100]: (k2_xboole_0(k2_tarski(A_98, B_99), k1_tarski(F_100))=k1_enumset1(A_98, B_99, F_100))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_169])).
% 1.98/1.19  tff(c_210, plain, (![A_110, B_111, F_112]: (k2_xboole_0(k2_tarski(A_110, B_111), k1_tarski(F_112))=k1_enumset1(B_111, A_110, F_112))), inference(superposition, [status(thm), theory('equality')], [c_6, c_173])).
% 1.98/1.19  tff(c_172, plain, (![A_29, B_30, F_97]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_tarski(F_97))=k1_enumset1(A_29, B_30, F_97))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_169])).
% 1.98/1.19  tff(c_216, plain, (![B_111, A_110, F_112]: (k1_enumset1(B_111, A_110, F_112)=k1_enumset1(A_110, B_111, F_112))), inference(superposition, [status(thm), theory('equality')], [c_210, c_172])).
% 1.98/1.19  tff(c_28, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.19  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_28])).
% 1.98/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  Inference rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Ref     : 0
% 1.98/1.19  #Sup     : 49
% 1.98/1.19  #Fact    : 0
% 1.98/1.19  #Define  : 0
% 1.98/1.19  #Split   : 0
% 1.98/1.19  #Chain   : 0
% 1.98/1.19  #Close   : 0
% 1.98/1.19  
% 1.98/1.19  Ordering : KBO
% 1.98/1.19  
% 1.98/1.19  Simplification rules
% 1.98/1.19  ----------------------
% 1.98/1.19  #Subsume      : 0
% 1.98/1.19  #Demod        : 9
% 1.98/1.19  #Tautology    : 41
% 1.98/1.19  #SimpNegUnit  : 0
% 1.98/1.19  #BackRed      : 1
% 1.98/1.19  
% 1.98/1.19  #Partial instantiations: 0
% 1.98/1.19  #Strategies tried      : 1
% 1.98/1.19  
% 1.98/1.19  Timing (in seconds)
% 1.98/1.19  ----------------------
% 1.98/1.19  Preprocessing        : 0.30
% 1.98/1.19  Parsing              : 0.16
% 1.98/1.19  CNF conversion       : 0.02
% 1.98/1.19  Main loop            : 0.14
% 1.98/1.19  Inferencing          : 0.06
% 1.98/1.19  Reduction            : 0.05
% 1.98/1.19  Demodulation         : 0.04
% 1.98/1.19  BG Simplification    : 0.02
% 1.98/1.19  Subsumption          : 0.02
% 1.98/1.19  Abstraction          : 0.01
% 1.98/1.19  MUC search           : 0.00
% 1.98/1.19  Cooper               : 0.00
% 1.98/1.19  Total                : 0.47
% 1.98/1.20  Index Insertion      : 0.00
% 1.98/1.20  Index Deletion       : 0.00
% 1.98/1.20  Index Matching       : 0.00
% 1.98/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
