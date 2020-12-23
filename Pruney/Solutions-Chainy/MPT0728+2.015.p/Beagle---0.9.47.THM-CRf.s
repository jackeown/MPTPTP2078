%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:57 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.23s
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
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_67,axiom,(
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

tff(f_70,negated_conjecture,(
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

tff(c_136,plain,(
    ! [A_77,B_78,C_79,D_80] : k3_enumset1(A_77,A_77,B_78,C_79,D_80) = k2_enumset1(A_77,B_78,C_79,D_80) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [E_26,A_22,B_23,G_30,D_25] : r2_hidden(G_30,k3_enumset1(A_22,B_23,G_30,D_25,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_160,plain,(
    ! [B_81,A_82,C_83,D_84] : r2_hidden(B_81,k2_enumset1(A_82,B_81,C_83,D_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_36])).

tff(c_164,plain,(
    ! [A_85,B_86,C_87] : r2_hidden(A_85,k1_enumset1(A_85,B_86,C_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_160])).

tff(c_177,plain,(
    ! [A_93,B_94] : r2_hidden(A_93,k2_tarski(A_93,B_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_164])).

tff(c_181,plain,(
    ! [A_95] : r2_hidden(A_95,k1_tarski(A_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_177])).

tff(c_66,plain,(
    ! [A_31] : k2_xboole_0(A_31,k1_tarski(A_31)) = k1_ordinal1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [D_36,B_37,A_38] :
      ( ~ r2_hidden(D_36,B_37)
      | r2_hidden(D_36,k2_xboole_0(A_38,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,(
    ! [D_36,A_31] :
      ( ~ r2_hidden(D_36,k1_tarski(A_31))
      | r2_hidden(D_36,k1_ordinal1(A_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_96])).

tff(c_185,plain,(
    ! [A_95] : r2_hidden(A_95,k1_ordinal1(A_95)) ),
    inference(resolution,[status(thm)],[c_181,c_99])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.23  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.21/1.23  
% 2.21/1.23  %Foreground sorts:
% 2.21/1.23  
% 2.21/1.23  
% 2.21/1.23  %Background operators:
% 2.21/1.23  
% 2.21/1.23  
% 2.21/1.23  %Foreground operators:
% 2.21/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.23  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.21/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.23  
% 2.23/1.24  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.24  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.23/1.24  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.23/1.24  tff(f_42, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.23/1.24  tff(f_65, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.23/1.24  tff(f_67, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.23/1.24  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.23/1.24  tff(f_70, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.23/1.24  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.23/1.24  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.23/1.24  tff(c_24, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.24  tff(c_136, plain, (![A_77, B_78, C_79, D_80]: (k3_enumset1(A_77, A_77, B_78, C_79, D_80)=k2_enumset1(A_77, B_78, C_79, D_80))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.24  tff(c_36, plain, (![E_26, A_22, B_23, G_30, D_25]: (r2_hidden(G_30, k3_enumset1(A_22, B_23, G_30, D_25, E_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.24  tff(c_160, plain, (![B_81, A_82, C_83, D_84]: (r2_hidden(B_81, k2_enumset1(A_82, B_81, C_83, D_84)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_36])).
% 2.23/1.24  tff(c_164, plain, (![A_85, B_86, C_87]: (r2_hidden(A_85, k1_enumset1(A_85, B_86, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_160])).
% 2.23/1.24  tff(c_177, plain, (![A_93, B_94]: (r2_hidden(A_93, k2_tarski(A_93, B_94)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_164])).
% 2.23/1.24  tff(c_181, plain, (![A_95]: (r2_hidden(A_95, k1_tarski(A_95)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_177])).
% 2.23/1.24  tff(c_66, plain, (![A_31]: (k2_xboole_0(A_31, k1_tarski(A_31))=k1_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.24  tff(c_96, plain, (![D_36, B_37, A_38]: (~r2_hidden(D_36, B_37) | r2_hidden(D_36, k2_xboole_0(A_38, B_37)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.24  tff(c_99, plain, (![D_36, A_31]: (~r2_hidden(D_36, k1_tarski(A_31)) | r2_hidden(D_36, k1_ordinal1(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_96])).
% 2.23/1.24  tff(c_185, plain, (![A_95]: (r2_hidden(A_95, k1_ordinal1(A_95)))), inference(resolution, [status(thm)], [c_181, c_99])).
% 2.23/1.24  tff(c_68, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.24  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_68])).
% 2.23/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  
% 2.23/1.24  Inference rules
% 2.23/1.24  ----------------------
% 2.23/1.24  #Ref     : 0
% 2.23/1.24  #Sup     : 27
% 2.23/1.24  #Fact    : 0
% 2.23/1.24  #Define  : 0
% 2.23/1.24  #Split   : 0
% 2.23/1.24  #Chain   : 0
% 2.23/1.24  #Close   : 0
% 2.23/1.24  
% 2.23/1.24  Ordering : KBO
% 2.23/1.24  
% 2.23/1.24  Simplification rules
% 2.23/1.24  ----------------------
% 2.23/1.24  #Subsume      : 0
% 2.23/1.24  #Demod        : 1
% 2.23/1.24  #Tautology    : 14
% 2.23/1.24  #SimpNegUnit  : 0
% 2.23/1.24  #BackRed      : 1
% 2.23/1.24  
% 2.23/1.24  #Partial instantiations: 0
% 2.23/1.24  #Strategies tried      : 1
% 2.23/1.24  
% 2.23/1.24  Timing (in seconds)
% 2.23/1.24  ----------------------
% 2.23/1.24  Preprocessing        : 0.31
% 2.23/1.24  Parsing              : 0.15
% 2.23/1.24  CNF conversion       : 0.02
% 2.23/1.24  Main loop            : 0.17
% 2.23/1.24  Inferencing          : 0.05
% 2.23/1.24  Reduction            : 0.05
% 2.23/1.24  Demodulation         : 0.04
% 2.23/1.24  BG Simplification    : 0.02
% 2.23/1.24  Subsumption          : 0.04
% 2.23/1.24  Abstraction          : 0.01
% 2.23/1.24  MUC search           : 0.00
% 2.23/1.24  Cooper               : 0.00
% 2.23/1.25  Total                : 0.50
% 2.23/1.25  Index Insertion      : 0.00
% 2.23/1.25  Index Deletion       : 0.00
% 2.23/1.25  Index Matching       : 0.00
% 2.23/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
