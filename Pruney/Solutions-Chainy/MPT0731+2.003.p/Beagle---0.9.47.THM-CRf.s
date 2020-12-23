%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:00 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   46 (  46 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_62,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_64,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_105,B_106,C_107,D_108] : k3_enumset1(A_105,A_105,B_106,C_107,D_108) = k2_enumset1(A_105,B_106,C_107,D_108) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [B_27,D_29,G_34,A_26,C_28] : r2_hidden(G_34,k3_enumset1(A_26,B_27,C_28,D_29,G_34)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [D_114,A_115,B_116,C_117] : r2_hidden(D_114,k2_enumset1(A_115,B_116,C_117,D_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_20])).

tff(c_250,plain,(
    ! [C_118,A_119,B_120] : r2_hidden(C_118,k1_enumset1(A_119,B_120,C_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_242])).

tff(c_258,plain,(
    ! [B_121,A_122] : r2_hidden(B_121,k2_tarski(A_122,B_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_250])).

tff(c_275,plain,(
    ! [A_129] : r2_hidden(A_129,k1_tarski(A_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_258])).

tff(c_56,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_279,plain,(
    ! [A_129] : ~ r1_tarski(k1_tarski(A_129),A_129) ),
    inference(resolution,[status(thm)],[c_275,c_56])).

tff(c_58,plain,(
    k1_ordinal1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    ! [A_35] : k2_xboole_0(A_35,k1_tarski(A_35)) = k1_ordinal1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_86,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_47,B_48] : r1_tarski(A_47,k2_xboole_0(B_48,A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_4])).

tff(c_151,plain,(
    ! [A_51] : r1_tarski(k1_tarski(A_51),k1_ordinal1(A_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_129])).

tff(c_154,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_151])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1 > #skF_3
% 2.43/1.36  
% 2.43/1.36  %Foreground sorts:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Background operators:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Foreground operators:
% 2.43/1.36  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.43/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.43/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.43/1.36  
% 2.53/1.37  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.37  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.53/1.37  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.53/1.37  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.53/1.37  tff(f_62, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.53/1.37  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.37  tff(f_73, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.53/1.37  tff(f_64, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.53/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.53/1.37  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.53/1.37  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.37  tff(c_8, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.37  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.37  tff(c_194, plain, (![A_105, B_106, C_107, D_108]: (k3_enumset1(A_105, A_105, B_106, C_107, D_108)=k2_enumset1(A_105, B_106, C_107, D_108))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.37  tff(c_20, plain, (![B_27, D_29, G_34, A_26, C_28]: (r2_hidden(G_34, k3_enumset1(A_26, B_27, C_28, D_29, G_34)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.37  tff(c_242, plain, (![D_114, A_115, B_116, C_117]: (r2_hidden(D_114, k2_enumset1(A_115, B_116, C_117, D_114)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_20])).
% 2.53/1.37  tff(c_250, plain, (![C_118, A_119, B_120]: (r2_hidden(C_118, k1_enumset1(A_119, B_120, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_242])).
% 2.53/1.37  tff(c_258, plain, (![B_121, A_122]: (r2_hidden(B_121, k2_tarski(A_122, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_250])).
% 2.53/1.37  tff(c_275, plain, (![A_129]: (r2_hidden(A_129, k1_tarski(A_129)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_258])).
% 2.53/1.37  tff(c_56, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.37  tff(c_279, plain, (![A_129]: (~r1_tarski(k1_tarski(A_129), A_129))), inference(resolution, [status(thm)], [c_275, c_56])).
% 2.53/1.37  tff(c_58, plain, (k1_ordinal1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.37  tff(c_54, plain, (![A_35]: (k2_xboole_0(A_35, k1_tarski(A_35))=k1_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.37  tff(c_86, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.37  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.37  tff(c_129, plain, (![A_47, B_48]: (r1_tarski(A_47, k2_xboole_0(B_48, A_47)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_4])).
% 2.53/1.37  tff(c_151, plain, (![A_51]: (r1_tarski(k1_tarski(A_51), k1_ordinal1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_129])).
% 2.53/1.37  tff(c_154, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_151])).
% 2.53/1.37  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_154])).
% 2.53/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  Inference rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Ref     : 0
% 2.53/1.37  #Sup     : 54
% 2.53/1.37  #Fact    : 0
% 2.53/1.37  #Define  : 0
% 2.53/1.37  #Split   : 0
% 2.53/1.37  #Chain   : 0
% 2.53/1.37  #Close   : 0
% 2.53/1.37  
% 2.53/1.37  Ordering : KBO
% 2.53/1.37  
% 2.53/1.37  Simplification rules
% 2.53/1.37  ----------------------
% 2.53/1.37  #Subsume      : 0
% 2.53/1.37  #Demod        : 3
% 2.53/1.37  #Tautology    : 27
% 2.53/1.37  #SimpNegUnit  : 1
% 2.53/1.37  #BackRed      : 1
% 2.53/1.37  
% 2.53/1.37  #Partial instantiations: 0
% 2.53/1.37  #Strategies tried      : 1
% 2.53/1.37  
% 2.53/1.37  Timing (in seconds)
% 2.53/1.37  ----------------------
% 2.53/1.38  Preprocessing        : 0.36
% 2.53/1.38  Parsing              : 0.18
% 2.53/1.38  CNF conversion       : 0.03
% 2.53/1.38  Main loop            : 0.21
% 2.53/1.38  Inferencing          : 0.07
% 2.53/1.38  Reduction            : 0.06
% 2.53/1.38  Demodulation         : 0.05
% 2.53/1.38  BG Simplification    : 0.02
% 2.53/1.38  Subsumption          : 0.05
% 2.53/1.38  Abstraction          : 0.02
% 2.53/1.38  MUC search           : 0.00
% 2.53/1.38  Cooper               : 0.00
% 2.53/1.38  Total                : 0.59
% 2.53/1.38  Index Insertion      : 0.00
% 2.53/1.38  Index Deletion       : 0.00
% 2.53/1.38  Index Matching       : 0.00
% 2.53/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
