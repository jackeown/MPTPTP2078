%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:57 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_72,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

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

tff(c_209,plain,(
    ! [E_108,C_104,A_105,D_107,B_106] : k4_enumset1(A_105,A_105,B_106,C_104,D_107,E_108) = k3_enumset1(A_105,B_106,C_104,D_107,E_108) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_24,B_25,F_29,C_26,H_33,E_28] : r2_hidden(H_33,k4_enumset1(A_24,B_25,C_26,H_33,E_28,F_29)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_262,plain,(
    ! [C_114,D_112,A_115,B_116,E_113] : r2_hidden(C_114,k3_enumset1(A_115,B_116,C_114,D_112,E_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_38])).

tff(c_266,plain,(
    ! [B_117,A_118,C_119,D_120] : r2_hidden(B_117,k2_enumset1(A_118,B_117,C_119,D_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_262])).

tff(c_270,plain,(
    ! [A_121,B_122,C_123] : r2_hidden(A_121,k1_enumset1(A_121,B_122,C_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_266])).

tff(c_295,plain,(
    ! [A_127,B_128] : r2_hidden(A_127,k2_tarski(A_127,B_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_270])).

tff(c_299,plain,(
    ! [A_129] : r2_hidden(A_129,k1_tarski(A_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_295])).

tff(c_74,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_tarski(A_34)) = k1_ordinal1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_133,plain,(
    ! [D_42,B_43,A_44] :
      ( ~ r2_hidden(D_42,B_43)
      | r2_hidden(D_42,k2_xboole_0(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_139,plain,(
    ! [D_42,A_34] :
      ( ~ r2_hidden(D_42,k1_tarski(A_34))
      | r2_hidden(D_42,k1_ordinal1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_133])).

tff(c_303,plain,(
    ! [A_129] : r2_hidden(A_129,k1_ordinal1(A_129)) ),
    inference(resolution,[status(thm)],[c_299,c_139])).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.33  
% 2.59/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.34  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.59/1.34  
% 2.59/1.34  %Foreground sorts:
% 2.59/1.34  
% 2.59/1.34  
% 2.59/1.34  %Background operators:
% 2.59/1.34  
% 2.59/1.34  
% 2.59/1.34  %Foreground operators:
% 2.59/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.34  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.59/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.59/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.59/1.34  
% 2.59/1.35  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.59/1.35  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.59/1.35  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.59/1.35  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.59/1.35  tff(f_44, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.59/1.35  tff(f_70, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 2.59/1.35  tff(f_72, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.59/1.35  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.59/1.35  tff(f_75, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.59/1.35  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.59/1.35  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.59/1.35  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.59/1.35  tff(c_26, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.35  tff(c_209, plain, (![E_108, C_104, A_105, D_107, B_106]: (k4_enumset1(A_105, A_105, B_106, C_104, D_107, E_108)=k3_enumset1(A_105, B_106, C_104, D_107, E_108))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.59/1.35  tff(c_38, plain, (![A_24, B_25, F_29, C_26, H_33, E_28]: (r2_hidden(H_33, k4_enumset1(A_24, B_25, C_26, H_33, E_28, F_29)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.59/1.35  tff(c_262, plain, (![C_114, D_112, A_115, B_116, E_113]: (r2_hidden(C_114, k3_enumset1(A_115, B_116, C_114, D_112, E_113)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_38])).
% 2.59/1.35  tff(c_266, plain, (![B_117, A_118, C_119, D_120]: (r2_hidden(B_117, k2_enumset1(A_118, B_117, C_119, D_120)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_262])).
% 2.59/1.35  tff(c_270, plain, (![A_121, B_122, C_123]: (r2_hidden(A_121, k1_enumset1(A_121, B_122, C_123)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_266])).
% 2.59/1.35  tff(c_295, plain, (![A_127, B_128]: (r2_hidden(A_127, k2_tarski(A_127, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_270])).
% 2.59/1.35  tff(c_299, plain, (![A_129]: (r2_hidden(A_129, k1_tarski(A_129)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_295])).
% 2.59/1.35  tff(c_74, plain, (![A_34]: (k2_xboole_0(A_34, k1_tarski(A_34))=k1_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.59/1.35  tff(c_133, plain, (![D_42, B_43, A_44]: (~r2_hidden(D_42, B_43) | r2_hidden(D_42, k2_xboole_0(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.59/1.35  tff(c_139, plain, (![D_42, A_34]: (~r2_hidden(D_42, k1_tarski(A_34)) | r2_hidden(D_42, k1_ordinal1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_133])).
% 2.59/1.35  tff(c_303, plain, (![A_129]: (r2_hidden(A_129, k1_ordinal1(A_129)))), inference(resolution, [status(thm)], [c_299, c_139])).
% 2.59/1.35  tff(c_76, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.59/1.35  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_303, c_76])).
% 2.59/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  Inference rules
% 2.59/1.35  ----------------------
% 2.59/1.35  #Ref     : 0
% 2.59/1.35  #Sup     : 53
% 2.59/1.35  #Fact    : 0
% 2.59/1.35  #Define  : 0
% 2.59/1.35  #Split   : 0
% 2.59/1.35  #Chain   : 0
% 2.59/1.35  #Close   : 0
% 2.59/1.35  
% 2.59/1.35  Ordering : KBO
% 2.59/1.35  
% 2.59/1.35  Simplification rules
% 2.59/1.35  ----------------------
% 2.59/1.35  #Subsume      : 3
% 2.59/1.35  #Demod        : 1
% 2.59/1.35  #Tautology    : 22
% 2.59/1.35  #SimpNegUnit  : 0
% 2.59/1.35  #BackRed      : 1
% 2.59/1.35  
% 2.59/1.35  #Partial instantiations: 0
% 2.59/1.35  #Strategies tried      : 1
% 2.59/1.35  
% 2.59/1.35  Timing (in seconds)
% 2.59/1.35  ----------------------
% 2.59/1.35  Preprocessing        : 0.35
% 2.59/1.35  Parsing              : 0.16
% 2.59/1.35  CNF conversion       : 0.03
% 2.59/1.35  Main loop            : 0.24
% 2.59/1.35  Inferencing          : 0.07
% 2.59/1.35  Reduction            : 0.07
% 2.59/1.35  Demodulation         : 0.05
% 2.59/1.35  BG Simplification    : 0.02
% 2.59/1.35  Subsumption          : 0.06
% 2.59/1.35  Abstraction          : 0.02
% 2.59/1.35  MUC search           : 0.00
% 2.59/1.35  Cooper               : 0.00
% 2.59/1.35  Total                : 0.61
% 2.59/1.35  Index Insertion      : 0.00
% 2.59/1.35  Index Deletion       : 0.00
% 2.59/1.35  Index Matching       : 0.00
% 2.59/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
