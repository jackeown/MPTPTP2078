%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:57 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k6_enumset1(A,A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_78,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_215,plain,(
    ! [C_132,A_133,E_136,D_135,B_134] : k6_enumset1(A_133,A_133,A_133,A_133,B_134,C_132,D_135,E_136) = k3_enumset1(A_133,B_134,C_132,D_135,E_136) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [A_24,H_31,B_25,F_29,D_27,C_26,E_28,J_35] : r2_hidden(J_35,k6_enumset1(A_24,B_25,C_26,D_27,E_28,F_29,J_35,H_31)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_248,plain,(
    ! [C_137,E_140,D_141,A_138,B_139] : r2_hidden(D_141,k3_enumset1(A_138,B_139,C_137,D_141,E_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_36])).

tff(c_252,plain,(
    ! [C_142,A_143,B_144,D_145] : r2_hidden(C_142,k2_enumset1(A_143,B_144,C_142,D_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_248])).

tff(c_256,plain,(
    ! [B_146,A_147,C_148] : r2_hidden(B_146,k1_enumset1(A_147,B_146,C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_252])).

tff(c_281,plain,(
    ! [A_152,B_153] : r2_hidden(A_152,k2_tarski(A_152,B_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_256])).

tff(c_285,plain,(
    ! [A_154] : r2_hidden(A_154,k1_tarski(A_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_281])).

tff(c_86,plain,(
    ! [A_36] : k2_xboole_0(A_36,k1_tarski(A_36)) = k1_ordinal1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_157,plain,(
    ! [D_49,B_50,A_51] :
      ( ~ r2_hidden(D_49,B_50)
      | r2_hidden(D_49,k2_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_163,plain,(
    ! [D_49,A_36] :
      ( ~ r2_hidden(D_49,k1_tarski(A_36))
      | r2_hidden(D_49,k1_ordinal1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_157])).

tff(c_289,plain,(
    ! [A_154] : r2_hidden(A_154,k1_ordinal1(A_154)) ),
    inference(resolution,[status(thm)],[c_285,c_163])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.33  %$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.38/1.33  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.33  
% 2.80/1.34  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.80/1.34  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.80/1.34  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.80/1.34  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.80/1.34  tff(f_44, axiom, (![A, B, C, D, E]: (k6_enumset1(A, A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_enumset1)).
% 2.80/1.34  tff(f_76, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 2.80/1.34  tff(f_78, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.80/1.34  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.80/1.34  tff(f_81, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.80/1.34  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.80/1.34  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.34  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.80/1.34  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.80/1.34  tff(c_215, plain, (![C_132, A_133, E_136, D_135, B_134]: (k6_enumset1(A_133, A_133, A_133, A_133, B_134, C_132, D_135, E_136)=k3_enumset1(A_133, B_134, C_132, D_135, E_136))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.34  tff(c_36, plain, (![A_24, H_31, B_25, F_29, D_27, C_26, E_28, J_35]: (r2_hidden(J_35, k6_enumset1(A_24, B_25, C_26, D_27, E_28, F_29, J_35, H_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.34  tff(c_248, plain, (![C_137, E_140, D_141, A_138, B_139]: (r2_hidden(D_141, k3_enumset1(A_138, B_139, C_137, D_141, E_140)))), inference(superposition, [status(thm), theory('equality')], [c_215, c_36])).
% 2.80/1.34  tff(c_252, plain, (![C_142, A_143, B_144, D_145]: (r2_hidden(C_142, k2_enumset1(A_143, B_144, C_142, D_145)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_248])).
% 2.80/1.34  tff(c_256, plain, (![B_146, A_147, C_148]: (r2_hidden(B_146, k1_enumset1(A_147, B_146, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_252])).
% 2.80/1.34  tff(c_281, plain, (![A_152, B_153]: (r2_hidden(A_152, k2_tarski(A_152, B_153)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_256])).
% 2.80/1.34  tff(c_285, plain, (![A_154]: (r2_hidden(A_154, k1_tarski(A_154)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_281])).
% 2.80/1.34  tff(c_86, plain, (![A_36]: (k2_xboole_0(A_36, k1_tarski(A_36))=k1_ordinal1(A_36))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.80/1.34  tff(c_157, plain, (![D_49, B_50, A_51]: (~r2_hidden(D_49, B_50) | r2_hidden(D_49, k2_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.80/1.34  tff(c_163, plain, (![D_49, A_36]: (~r2_hidden(D_49, k1_tarski(A_36)) | r2_hidden(D_49, k1_ordinal1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_157])).
% 2.80/1.34  tff(c_289, plain, (![A_154]: (r2_hidden(A_154, k1_ordinal1(A_154)))), inference(resolution, [status(thm)], [c_285, c_163])).
% 2.80/1.34  tff(c_88, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.34  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_88])).
% 2.80/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.34  
% 2.80/1.34  Inference rules
% 2.80/1.34  ----------------------
% 2.80/1.34  #Ref     : 0
% 2.80/1.34  #Sup     : 48
% 2.80/1.34  #Fact    : 0
% 2.80/1.34  #Define  : 0
% 2.80/1.34  #Split   : 0
% 2.80/1.34  #Chain   : 0
% 2.80/1.34  #Close   : 0
% 2.80/1.34  
% 2.80/1.34  Ordering : KBO
% 2.80/1.34  
% 2.80/1.34  Simplification rules
% 2.80/1.34  ----------------------
% 2.80/1.34  #Subsume      : 2
% 2.80/1.34  #Demod        : 1
% 2.80/1.34  #Tautology    : 21
% 2.80/1.34  #SimpNegUnit  : 0
% 2.80/1.34  #BackRed      : 1
% 2.80/1.34  
% 2.80/1.34  #Partial instantiations: 0
% 2.80/1.34  #Strategies tried      : 1
% 2.80/1.34  
% 2.80/1.34  Timing (in seconds)
% 2.80/1.34  ----------------------
% 2.80/1.34  Preprocessing        : 0.34
% 2.80/1.34  Parsing              : 0.16
% 2.80/1.34  CNF conversion       : 0.03
% 2.80/1.34  Main loop            : 0.24
% 2.80/1.34  Inferencing          : 0.07
% 2.80/1.34  Reduction            : 0.06
% 2.80/1.34  Demodulation         : 0.05
% 2.80/1.34  BG Simplification    : 0.02
% 2.80/1.34  Subsumption          : 0.08
% 2.80/1.34  Abstraction          : 0.02
% 2.80/1.34  MUC search           : 0.00
% 2.80/1.34  Cooper               : 0.00
% 2.80/1.34  Total                : 0.61
% 2.80/1.34  Index Insertion      : 0.00
% 2.80/1.34  Index Deletion       : 0.00
% 2.80/1.34  Index Matching       : 0.00
% 2.80/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
