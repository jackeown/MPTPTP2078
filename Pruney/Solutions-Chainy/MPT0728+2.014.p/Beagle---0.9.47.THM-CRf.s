%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:57 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_67,axiom,(
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

tff(f_70,negated_conjecture,(
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

tff(c_163,plain,(
    ! [A_76,B_77,C_78,D_79] : k3_enumset1(A_76,A_76,B_77,C_78,D_79) = k2_enumset1(A_76,B_77,C_78,D_79) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_19,G_27,D_22,B_20,E_23] : r2_hidden(G_27,k3_enumset1(A_19,B_20,G_27,D_22,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_187,plain,(
    ! [B_80,A_81,C_82,D_83] : r2_hidden(B_80,k2_enumset1(A_81,B_80,C_82,D_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_36])).

tff(c_191,plain,(
    ! [A_84,B_85,C_86] : r2_hidden(A_84,k1_enumset1(A_84,B_85,C_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_187])).

tff(c_195,plain,(
    ! [A_87,B_88] : r2_hidden(A_87,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_191])).

tff(c_199,plain,(
    ! [A_89] : r2_hidden(A_89,k1_tarski(A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_195])).

tff(c_66,plain,(
    ! [A_28] : k2_xboole_0(A_28,k1_tarski(A_28)) = k1_ordinal1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_126,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | r2_hidden(D_41,k2_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_132,plain,(
    ! [D_41,A_28] :
      ( ~ r2_hidden(D_41,k1_tarski(A_28))
      | r2_hidden(D_41,k1_ordinal1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_126])).

tff(c_203,plain,(
    ! [A_89] : r2_hidden(A_89,k1_ordinal1(A_89)) ),
    inference(resolution,[status(thm)],[c_199,c_132])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.15/1.25  
% 2.15/1.25  %Foreground sorts:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Background operators:
% 2.15/1.25  
% 2.15/1.25  
% 2.15/1.25  %Foreground operators:
% 2.15/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.25  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  
% 2.15/1.26  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.26  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.26  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.15/1.26  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.15/1.26  tff(f_65, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 2.15/1.26  tff(f_67, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.15/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.15/1.26  tff(f_70, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.15/1.26  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.15/1.26  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.15/1.26  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.26  tff(c_163, plain, (![A_76, B_77, C_78, D_79]: (k3_enumset1(A_76, A_76, B_77, C_78, D_79)=k2_enumset1(A_76, B_77, C_78, D_79))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.26  tff(c_36, plain, (![A_19, G_27, D_22, B_20, E_23]: (r2_hidden(G_27, k3_enumset1(A_19, B_20, G_27, D_22, E_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.15/1.26  tff(c_187, plain, (![B_80, A_81, C_82, D_83]: (r2_hidden(B_80, k2_enumset1(A_81, B_80, C_82, D_83)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_36])).
% 2.15/1.26  tff(c_191, plain, (![A_84, B_85, C_86]: (r2_hidden(A_84, k1_enumset1(A_84, B_85, C_86)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_187])).
% 2.15/1.26  tff(c_195, plain, (![A_87, B_88]: (r2_hidden(A_87, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_191])).
% 2.15/1.26  tff(c_199, plain, (![A_89]: (r2_hidden(A_89, k1_tarski(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_195])).
% 2.15/1.26  tff(c_66, plain, (![A_28]: (k2_xboole_0(A_28, k1_tarski(A_28))=k1_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.26  tff(c_126, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | r2_hidden(D_41, k2_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.26  tff(c_132, plain, (![D_41, A_28]: (~r2_hidden(D_41, k1_tarski(A_28)) | r2_hidden(D_41, k1_ordinal1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_126])).
% 2.15/1.26  tff(c_203, plain, (![A_89]: (r2_hidden(A_89, k1_ordinal1(A_89)))), inference(resolution, [status(thm)], [c_199, c_132])).
% 2.15/1.26  tff(c_68, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.15/1.26  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_68])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 32
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 0
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 2
% 2.15/1.26  #Demod        : 1
% 2.15/1.26  #Tautology    : 16
% 2.15/1.26  #SimpNegUnit  : 0
% 2.15/1.26  #BackRed      : 1
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.27  Preprocessing        : 0.32
% 2.15/1.27  Parsing              : 0.16
% 2.15/1.27  CNF conversion       : 0.02
% 2.15/1.27  Main loop            : 0.18
% 2.15/1.27  Inferencing          : 0.05
% 2.15/1.27  Reduction            : 0.05
% 2.15/1.27  Demodulation         : 0.04
% 2.15/1.27  BG Simplification    : 0.02
% 2.15/1.27  Subsumption          : 0.05
% 2.15/1.27  Abstraction          : 0.02
% 2.15/1.27  MUC search           : 0.00
% 2.15/1.27  Cooper               : 0.00
% 2.15/1.27  Total                : 0.52
% 2.15/1.27  Index Insertion      : 0.00
% 2.15/1.27  Index Deletion       : 0.00
% 2.15/1.27  Index Matching       : 0.00
% 2.15/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
