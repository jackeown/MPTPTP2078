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
% DateTime   : Thu Dec  3 09:52:03 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63,plain,(
    ! [A_35] : k1_enumset1(A_35,A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_24])).

tff(c_56,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,(
    ! [D_48,A_49,B_50] :
      ( r2_hidden(D_48,A_49)
      | ~ r2_hidden(D_48,k3_xboole_0(A_49,B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_6])).

tff(c_112,plain,(
    ! [D_51] :
      ( r2_hidden(D_51,'#skF_5')
      | ~ r2_hidden(D_51,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_108])).

tff(c_116,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_69,c_112])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.85/1.19  
% 1.85/1.19  %Foreground sorts:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Background operators:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Foreground operators:
% 1.85/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.85/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.85/1.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.85/1.19  
% 1.85/1.20  tff(f_65, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.85/1.20  tff(f_60, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 1.85/1.20  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.85/1.20  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.85/1.20  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.85/1.20  tff(c_54, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.20  tff(c_63, plain, (![A_35]: (k1_enumset1(A_35, A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.20  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.20  tff(c_69, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_24])).
% 1.85/1.20  tff(c_56, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.85/1.20  tff(c_86, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.20  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.20  tff(c_108, plain, (![D_48, A_49, B_50]: (r2_hidden(D_48, A_49) | ~r2_hidden(D_48, k3_xboole_0(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_6])).
% 1.85/1.20  tff(c_112, plain, (![D_51]: (r2_hidden(D_51, '#skF_5') | ~r2_hidden(D_51, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_108])).
% 1.85/1.20  tff(c_116, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_69, c_112])).
% 1.85/1.20  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_116])).
% 1.85/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  Inference rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Ref     : 0
% 1.85/1.20  #Sup     : 15
% 1.85/1.20  #Fact    : 0
% 1.85/1.20  #Define  : 0
% 1.85/1.20  #Split   : 0
% 1.85/1.20  #Chain   : 0
% 1.85/1.20  #Close   : 0
% 1.85/1.20  
% 1.85/1.20  Ordering : KBO
% 1.85/1.20  
% 1.85/1.20  Simplification rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Subsume      : 0
% 1.85/1.20  #Demod        : 2
% 1.85/1.20  #Tautology    : 8
% 1.85/1.20  #SimpNegUnit  : 1
% 1.85/1.20  #BackRed      : 0
% 1.85/1.20  
% 1.85/1.20  #Partial instantiations: 0
% 1.85/1.20  #Strategies tried      : 1
% 1.85/1.20  
% 1.85/1.20  Timing (in seconds)
% 1.85/1.20  ----------------------
% 1.85/1.20  Preprocessing        : 0.31
% 1.85/1.20  Parsing              : 0.15
% 1.85/1.20  CNF conversion       : 0.03
% 1.85/1.20  Main loop            : 0.12
% 1.85/1.20  Inferencing          : 0.03
% 1.85/1.20  Reduction            : 0.04
% 1.85/1.20  Demodulation         : 0.03
% 1.85/1.20  BG Simplification    : 0.01
% 1.85/1.20  Subsumption          : 0.03
% 1.85/1.20  Abstraction          : 0.01
% 1.85/1.20  MUC search           : 0.00
% 1.85/1.20  Cooper               : 0.00
% 1.85/1.20  Total                : 0.45
% 1.85/1.20  Index Insertion      : 0.00
% 1.85/1.20  Index Deletion       : 0.00
% 1.85/1.20  Index Matching       : 0.00
% 1.85/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
