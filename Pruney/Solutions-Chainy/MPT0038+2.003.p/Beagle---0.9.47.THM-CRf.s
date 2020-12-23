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
% DateTime   : Thu Dec  3 09:42:42 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  29 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_15,B_16,C_17] : r1_tarski(k3_xboole_0(A_15,B_16),k2_xboole_0(A_15,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [B_4,A_3,C_17] : r1_tarski(k3_xboole_0(B_4,A_3),k2_xboole_0(A_3,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [B_21,A_22,C_23] : r1_tarski(k3_xboole_0(B_21,A_22),k2_xboole_0(A_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_113,plain,(
    ! [B_21,B_2,A_1] : r1_tarski(k3_xboole_0(B_21,B_2),k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_140,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(k2_xboole_0(A_27,C_28),B_29)
      | ~ r1_tarski(C_28,B_29)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_1','#skF_2')),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_10])).

tff(c_143,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_140,c_11])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_113,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:34:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.14  
% 1.62/1.15  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.62/1.15  tff(f_31, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.62/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.62/1.15  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.62/1.15  tff(f_40, negated_conjecture, ~(![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.62/1.15  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.15  tff(c_78, plain, (![A_15, B_16, C_17]: (r1_tarski(k3_xboole_0(A_15, B_16), k2_xboole_0(A_15, C_17)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.15  tff(c_87, plain, (![B_4, A_3, C_17]: (r1_tarski(k3_xboole_0(B_4, A_3), k2_xboole_0(A_3, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78])).
% 1.62/1.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.15  tff(c_107, plain, (![B_21, A_22, C_23]: (r1_tarski(k3_xboole_0(B_21, A_22), k2_xboole_0(A_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78])).
% 1.62/1.15  tff(c_113, plain, (![B_21, B_2, A_1]: (r1_tarski(k3_xboole_0(B_21, B_2), k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 1.62/1.15  tff(c_140, plain, (![A_27, C_28, B_29]: (r1_tarski(k2_xboole_0(A_27, C_28), B_29) | ~r1_tarski(C_28, B_29) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.15  tff(c_10, plain, (~r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3')), k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.15  tff(c_11, plain, (~r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_1', '#skF_2')), k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_10])).
% 1.62/1.15  tff(c_143, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_140, c_11])).
% 1.62/1.15  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_113, c_143])).
% 1.62/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  Inference rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Ref     : 0
% 1.62/1.15  #Sup     : 35
% 1.62/1.15  #Fact    : 0
% 1.62/1.15  #Define  : 0
% 1.62/1.15  #Split   : 0
% 1.62/1.15  #Chain   : 0
% 1.62/1.15  #Close   : 0
% 1.62/1.15  
% 1.62/1.15  Ordering : KBO
% 1.62/1.15  
% 1.62/1.15  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 0
% 1.62/1.15  #Demod        : 14
% 1.62/1.15  #Tautology    : 26
% 1.62/1.15  #SimpNegUnit  : 0
% 1.62/1.15  #BackRed      : 0
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.15  Preprocessing        : 0.26
% 1.62/1.15  Parsing              : 0.14
% 1.62/1.15  CNF conversion       : 0.01
% 1.62/1.15  Main loop            : 0.14
% 1.62/1.15  Inferencing          : 0.05
% 1.62/1.15  Reduction            : 0.06
% 1.62/1.15  Demodulation         : 0.05
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.02
% 1.62/1.15  Abstraction          : 0.01
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.42
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
