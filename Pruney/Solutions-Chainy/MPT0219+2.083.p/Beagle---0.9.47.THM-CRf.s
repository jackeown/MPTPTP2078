%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:00 EST 2020

% Result     : Theorem 9.31s
% Output     : CNFRefutation 9.31s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_66,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_187,plain,(
    ! [A_86,B_87] : k2_xboole_0(k1_tarski(A_86),k1_tarski(B_87)) = k2_tarski(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_197,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_68])).

tff(c_149,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_158,plain,(
    ! [B_78,A_77] : r2_hidden(B_78,k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_28])).

tff(c_215,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_158])).

tff(c_54,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1078,plain,(
    ! [E_121,C_122,B_123,A_124] :
      ( E_121 = C_122
      | E_121 = B_123
      | E_121 = A_124
      | ~ r2_hidden(E_121,k1_enumset1(A_124,B_123,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9797,plain,(
    ! [E_243,B_244,A_245] :
      ( E_243 = B_244
      | E_243 = A_245
      | E_243 = A_245
      | ~ r2_hidden(E_243,k2_tarski(A_245,B_244)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1078])).

tff(c_9859,plain,(
    ! [E_247,A_248] :
      ( E_247 = A_248
      | E_247 = A_248
      | E_247 = A_248
      | ~ r2_hidden(E_247,k1_tarski(A_248)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_9797])).

tff(c_9870,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_215,c_9859])).

tff(c_9879,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_66,c_9870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.31/3.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.47  
% 9.31/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.47  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.31/3.47  
% 9.31/3.47  %Foreground sorts:
% 9.31/3.47  
% 9.31/3.47  
% 9.31/3.47  %Background operators:
% 9.31/3.47  
% 9.31/3.47  
% 9.31/3.47  %Foreground operators:
% 9.31/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.31/3.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.31/3.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.31/3.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.31/3.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.31/3.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.31/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.31/3.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.31/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.31/3.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.31/3.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.31/3.47  tff('#skF_3', type, '#skF_3': $i).
% 9.31/3.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.31/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.31/3.47  tff('#skF_4', type, '#skF_4': $i).
% 9.31/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.31/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.31/3.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.31/3.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.31/3.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.31/3.47  
% 9.31/3.48  tff(f_89, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 9.31/3.48  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 9.31/3.48  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.31/3.48  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.31/3.48  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.31/3.48  tff(c_66, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.31/3.48  tff(c_187, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), k1_tarski(B_87))=k2_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.31/3.48  tff(c_68, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.31/3.48  tff(c_197, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_187, c_68])).
% 9.31/3.48  tff(c_149, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.31/3.48  tff(c_28, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.31/3.48  tff(c_158, plain, (![B_78, A_77]: (r2_hidden(B_78, k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_28])).
% 9.31/3.48  tff(c_215, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_158])).
% 9.31/3.48  tff(c_54, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.31/3.48  tff(c_56, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.31/3.48  tff(c_1078, plain, (![E_121, C_122, B_123, A_124]: (E_121=C_122 | E_121=B_123 | E_121=A_124 | ~r2_hidden(E_121, k1_enumset1(A_124, B_123, C_122)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.31/3.48  tff(c_9797, plain, (![E_243, B_244, A_245]: (E_243=B_244 | E_243=A_245 | E_243=A_245 | ~r2_hidden(E_243, k2_tarski(A_245, B_244)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1078])).
% 9.31/3.48  tff(c_9859, plain, (![E_247, A_248]: (E_247=A_248 | E_247=A_248 | E_247=A_248 | ~r2_hidden(E_247, k1_tarski(A_248)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_9797])).
% 9.31/3.48  tff(c_9870, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_215, c_9859])).
% 9.31/3.48  tff(c_9879, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_9870])).
% 9.31/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.48  
% 9.31/3.48  Inference rules
% 9.31/3.48  ----------------------
% 9.31/3.48  #Ref     : 0
% 9.31/3.48  #Sup     : 2584
% 9.31/3.48  #Fact    : 0
% 9.31/3.48  #Define  : 0
% 9.31/3.48  #Split   : 0
% 9.31/3.48  #Chain   : 0
% 9.31/3.48  #Close   : 0
% 9.31/3.48  
% 9.31/3.48  Ordering : KBO
% 9.31/3.48  
% 9.31/3.48  Simplification rules
% 9.31/3.48  ----------------------
% 9.31/3.48  #Subsume      : 168
% 9.31/3.48  #Demod        : 2395
% 9.31/3.48  #Tautology    : 632
% 9.31/3.48  #SimpNegUnit  : 3
% 9.31/3.48  #BackRed      : 5
% 9.31/3.48  
% 9.31/3.48  #Partial instantiations: 0
% 9.31/3.48  #Strategies tried      : 1
% 9.31/3.48  
% 9.31/3.48  Timing (in seconds)
% 9.31/3.48  ----------------------
% 9.31/3.48  Preprocessing        : 0.35
% 9.31/3.48  Parsing              : 0.18
% 9.31/3.48  CNF conversion       : 0.03
% 9.31/3.48  Main loop            : 2.37
% 9.31/3.48  Inferencing          : 0.44
% 9.31/3.48  Reduction            : 1.51
% 9.31/3.48  Demodulation         : 1.39
% 9.31/3.48  BG Simplification    : 0.08
% 9.31/3.48  Subsumption          : 0.26
% 9.31/3.48  Abstraction          : 0.11
% 9.31/3.48  MUC search           : 0.00
% 9.31/3.48  Cooper               : 0.00
% 9.31/3.48  Total                : 2.74
% 9.31/3.48  Index Insertion      : 0.00
% 9.31/3.48  Index Deletion       : 0.00
% 9.31/3.49  Index Matching       : 0.00
% 9.31/3.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
