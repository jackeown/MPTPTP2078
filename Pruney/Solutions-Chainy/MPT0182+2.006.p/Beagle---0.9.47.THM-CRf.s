%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:43 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   20 (  35 expanded)
%              Number of equality atoms :   19 (  34 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_45,B_46,C_47] : k2_enumset1(A_45,A_45,B_46,C_47) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_48,B_49,C_50,D_51] : k3_enumset1(A_48,A_48,B_49,C_50,D_51) = k2_enumset1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [C_85,B_88,D_87,A_84,E_86] : k2_xboole_0(k2_enumset1(A_84,B_88,C_85,D_87),k1_tarski(E_86)) = k3_enumset1(A_84,B_88,C_85,D_87,E_86) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_45,B_46,C_47,E_86] : k3_enumset1(A_45,A_45,B_46,C_47,E_86) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),k1_tarski(E_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_127])).

tff(c_140,plain,(
    ! [A_89,B_90,C_91,E_92] : k2_xboole_0(k1_enumset1(A_89,B_90,C_91),k1_tarski(E_92)) = k2_enumset1(A_89,B_90,C_91,E_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_136])).

tff(c_149,plain,(
    ! [A_43,B_44,E_92] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(E_92)) = k2_enumset1(A_43,A_43,B_44,E_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_140])).

tff(c_153,plain,(
    ! [A_93,B_94,E_95] : k2_xboole_0(k2_tarski(A_93,B_94),k1_tarski(E_95)) = k1_enumset1(A_93,B_94,E_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_181,plain,(
    ! [B_98,A_99,E_100] : k2_xboole_0(k2_tarski(B_98,A_99),k1_tarski(E_100)) = k1_enumset1(A_99,B_98,E_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_152,plain,(
    ! [A_43,B_44,E_92] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(E_92)) = k1_enumset1(A_43,B_44,E_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_187,plain,(
    ! [B_98,A_99,E_100] : k1_enumset1(B_98,A_99,E_100) = k1_enumset1(A_99,B_98,E_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_152])).

tff(c_30,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.17/1.34  
% 2.17/1.34  %Foreground sorts:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Background operators:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Foreground operators:
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.34  
% 2.17/1.35  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.35  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.17/1.35  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.35  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.17/1.35  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.17/1.35  tff(f_56, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.17/1.35  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.35  tff(c_22, plain, (![A_45, B_46, C_47]: (k2_enumset1(A_45, A_45, B_46, C_47)=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.35  tff(c_20, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.35  tff(c_24, plain, (![A_48, B_49, C_50, D_51]: (k3_enumset1(A_48, A_48, B_49, C_50, D_51)=k2_enumset1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.35  tff(c_127, plain, (![C_85, B_88, D_87, A_84, E_86]: (k2_xboole_0(k2_enumset1(A_84, B_88, C_85, D_87), k1_tarski(E_86))=k3_enumset1(A_84, B_88, C_85, D_87, E_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.35  tff(c_136, plain, (![A_45, B_46, C_47, E_86]: (k3_enumset1(A_45, A_45, B_46, C_47, E_86)=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), k1_tarski(E_86)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_127])).
% 2.17/1.35  tff(c_140, plain, (![A_89, B_90, C_91, E_92]: (k2_xboole_0(k1_enumset1(A_89, B_90, C_91), k1_tarski(E_92))=k2_enumset1(A_89, B_90, C_91, E_92))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_136])).
% 2.17/1.35  tff(c_149, plain, (![A_43, B_44, E_92]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(E_92))=k2_enumset1(A_43, A_43, B_44, E_92))), inference(superposition, [status(thm), theory('equality')], [c_20, c_140])).
% 2.17/1.35  tff(c_153, plain, (![A_93, B_94, E_95]: (k2_xboole_0(k2_tarski(A_93, B_94), k1_tarski(E_95))=k1_enumset1(A_93, B_94, E_95))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_149])).
% 2.17/1.35  tff(c_181, plain, (![B_98, A_99, E_100]: (k2_xboole_0(k2_tarski(B_98, A_99), k1_tarski(E_100))=k1_enumset1(A_99, B_98, E_100))), inference(superposition, [status(thm), theory('equality')], [c_6, c_153])).
% 2.17/1.35  tff(c_152, plain, (![A_43, B_44, E_92]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(E_92))=k1_enumset1(A_43, B_44, E_92))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_149])).
% 2.17/1.35  tff(c_187, plain, (![B_98, A_99, E_100]: (k1_enumset1(B_98, A_99, E_100)=k1_enumset1(A_99, B_98, E_100))), inference(superposition, [status(thm), theory('equality')], [c_181, c_152])).
% 2.17/1.35  tff(c_30, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.35  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_30])).
% 2.17/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  
% 2.17/1.35  Inference rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Ref     : 0
% 2.17/1.35  #Sup     : 42
% 2.17/1.35  #Fact    : 0
% 2.17/1.35  #Define  : 0
% 2.17/1.35  #Split   : 0
% 2.17/1.35  #Chain   : 0
% 2.17/1.35  #Close   : 0
% 2.17/1.35  
% 2.17/1.35  Ordering : KBO
% 2.17/1.35  
% 2.17/1.35  Simplification rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Subsume      : 0
% 2.17/1.35  #Demod        : 8
% 2.17/1.35  #Tautology    : 35
% 2.17/1.35  #SimpNegUnit  : 0
% 2.17/1.35  #BackRed      : 1
% 2.17/1.35  
% 2.17/1.35  #Partial instantiations: 0
% 2.17/1.35  #Strategies tried      : 1
% 2.17/1.35  
% 2.17/1.35  Timing (in seconds)
% 2.17/1.35  ----------------------
% 2.17/1.36  Preprocessing        : 0.36
% 2.17/1.36  Parsing              : 0.19
% 2.17/1.36  CNF conversion       : 0.02
% 2.17/1.36  Main loop            : 0.14
% 2.17/1.36  Inferencing          : 0.05
% 2.17/1.36  Reduction            : 0.05
% 2.17/1.36  Demodulation         : 0.04
% 2.17/1.36  BG Simplification    : 0.02
% 2.17/1.36  Subsumption          : 0.02
% 2.17/1.36  Abstraction          : 0.01
% 2.17/1.36  MUC search           : 0.00
% 2.17/1.36  Cooper               : 0.00
% 2.17/1.36  Total                : 0.52
% 2.17/1.36  Index Insertion      : 0.00
% 2.17/1.36  Index Deletion       : 0.00
% 2.17/1.36  Index Matching       : 0.00
% 2.17/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
