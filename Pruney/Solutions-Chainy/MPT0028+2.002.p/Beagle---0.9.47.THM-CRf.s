%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:35 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  36 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_27,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski('#skF_1'(A_5,B_6,C_7),B_6)
      | k3_xboole_0(B_6,C_7) = A_5
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_tarski('#skF_1'(A_23,B_24,C_25),A_23)
      | k3_xboole_0(B_24,C_25) = A_23
      | ~ r1_tarski(A_23,C_25)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [B_6,C_7] :
      ( k3_xboole_0(B_6,C_7) = B_6
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(B_6,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_79,plain,(
    ! [B_26,C_27] :
      ( k3_xboole_0(B_26,C_27) = B_26
      | ~ r1_tarski(B_26,C_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_68])).

tff(c_97,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = A_9 ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_14,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.12  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.76/1.12  
% 1.76/1.12  %Foreground sorts:
% 1.76/1.12  
% 1.76/1.12  
% 1.76/1.12  %Background operators:
% 1.76/1.12  
% 1.76/1.12  
% 1.76/1.12  %Foreground operators:
% 1.76/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.76/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.12  
% 1.76/1.13  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.76/1.13  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.76/1.13  tff(f_42, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.76/1.13  tff(f_47, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.76/1.13  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.13  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.13  tff(c_24, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.13  tff(c_27, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 1.76/1.13  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski('#skF_1'(A_5, B_6, C_7), B_6) | k3_xboole_0(B_6, C_7)=A_5 | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.76/1.13  tff(c_64, plain, (![A_23, B_24, C_25]: (~r1_tarski('#skF_1'(A_23, B_24, C_25), A_23) | k3_xboole_0(B_24, C_25)=A_23 | ~r1_tarski(A_23, C_25) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.76/1.13  tff(c_68, plain, (![B_6, C_7]: (k3_xboole_0(B_6, C_7)=B_6 | ~r1_tarski(B_6, C_7) | ~r1_tarski(B_6, B_6))), inference(resolution, [status(thm)], [c_10, c_64])).
% 1.76/1.13  tff(c_79, plain, (![B_26, C_27]: (k3_xboole_0(B_26, C_27)=B_26 | ~r1_tarski(B_26, C_27))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_68])).
% 1.76/1.13  tff(c_97, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=A_9)), inference(resolution, [status(thm)], [c_12, c_79])).
% 1.76/1.13  tff(c_14, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.76/1.13  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_14])).
% 1.76/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.13  
% 1.76/1.13  Inference rules
% 1.76/1.13  ----------------------
% 1.76/1.13  #Ref     : 0
% 1.76/1.13  #Sup     : 17
% 1.76/1.13  #Fact    : 0
% 1.76/1.13  #Define  : 0
% 1.76/1.13  #Split   : 0
% 1.76/1.13  #Chain   : 0
% 1.76/1.13  #Close   : 0
% 1.76/1.13  
% 1.76/1.13  Ordering : KBO
% 1.76/1.13  
% 1.76/1.13  Simplification rules
% 1.76/1.13  ----------------------
% 1.76/1.13  #Subsume      : 0
% 1.76/1.13  #Demod        : 5
% 1.76/1.13  #Tautology    : 10
% 1.76/1.13  #SimpNegUnit  : 0
% 1.76/1.13  #BackRed      : 1
% 1.76/1.13  
% 1.76/1.13  #Partial instantiations: 0
% 1.76/1.13  #Strategies tried      : 1
% 1.76/1.13  
% 1.76/1.13  Timing (in seconds)
% 1.76/1.13  ----------------------
% 1.76/1.13  Preprocessing        : 0.25
% 1.76/1.13  Parsing              : 0.14
% 1.76/1.13  CNF conversion       : 0.02
% 1.76/1.13  Main loop            : 0.12
% 1.76/1.13  Inferencing          : 0.05
% 1.76/1.13  Reduction            : 0.03
% 1.76/1.13  Demodulation         : 0.03
% 1.76/1.13  BG Simplification    : 0.01
% 1.76/1.14  Subsumption          : 0.02
% 1.76/1.14  Abstraction          : 0.01
% 1.76/1.14  MUC search           : 0.00
% 1.76/1.14  Cooper               : 0.00
% 1.76/1.14  Total                : 0.40
% 1.76/1.14  Index Insertion      : 0.00
% 1.76/1.14  Index Deletion       : 0.00
% 1.76/1.14  Index Matching       : 0.00
% 1.76/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
