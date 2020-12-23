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
% DateTime   : Thu Dec  3 09:42:44 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [C_8,B_9,A_10] :
      ( r1_tarski(k4_xboole_0(C_8,B_9),k4_xboole_0(C_8,A_10))
      | ~ r1_tarski(A_10,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25,plain,(
    ! [A_5,B_9] :
      ( r1_tarski(k4_xboole_0(A_5,B_9),A_5)
      | ~ r1_tarski(k1_xboole_0,B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_19])).

tff(c_27,plain,(
    ! [A_5,B_9] : r1_tarski(k4_xboole_0(A_5,B_9),A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_25])).

tff(c_8,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:45:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.04  
% 1.46/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.05  %$ r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.46/1.05  
% 1.46/1.05  %Foreground sorts:
% 1.46/1.05  
% 1.46/1.05  
% 1.46/1.05  %Background operators:
% 1.46/1.05  
% 1.46/1.05  
% 1.46/1.05  %Foreground operators:
% 1.46/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.46/1.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.46/1.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.46/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.46/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.46/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.46/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.46/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.46/1.05  
% 1.46/1.06  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.46/1.06  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.46/1.06  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 1.46/1.06  tff(f_36, negated_conjecture, ~(![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.46/1.06  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.46/1.06  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.46/1.06  tff(c_19, plain, (![C_8, B_9, A_10]: (r1_tarski(k4_xboole_0(C_8, B_9), k4_xboole_0(C_8, A_10)) | ~r1_tarski(A_10, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.46/1.06  tff(c_25, plain, (![A_5, B_9]: (r1_tarski(k4_xboole_0(A_5, B_9), A_5) | ~r1_tarski(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_6, c_19])).
% 1.46/1.06  tff(c_27, plain, (![A_5, B_9]: (r1_tarski(k4_xboole_0(A_5, B_9), A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_25])).
% 1.46/1.06  tff(c_8, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.46/1.06  tff(c_30, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27, c_8])).
% 1.46/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.06  
% 1.46/1.06  Inference rules
% 1.46/1.06  ----------------------
% 1.46/1.06  #Ref     : 0
% 1.46/1.06  #Sup     : 4
% 1.46/1.06  #Fact    : 0
% 1.46/1.06  #Define  : 0
% 1.46/1.06  #Split   : 0
% 1.46/1.06  #Chain   : 0
% 1.46/1.06  #Close   : 0
% 1.46/1.06  
% 1.46/1.06  Ordering : KBO
% 1.46/1.06  
% 1.46/1.06  Simplification rules
% 1.46/1.06  ----------------------
% 1.46/1.06  #Subsume      : 0
% 1.46/1.06  #Demod        : 2
% 1.46/1.06  #Tautology    : 2
% 1.46/1.06  #SimpNegUnit  : 0
% 1.46/1.06  #BackRed      : 1
% 1.46/1.06  
% 1.46/1.06  #Partial instantiations: 0
% 1.46/1.06  #Strategies tried      : 1
% 1.46/1.06  
% 1.46/1.06  Timing (in seconds)
% 1.46/1.06  ----------------------
% 1.46/1.06  Preprocessing        : 0.24
% 1.46/1.06  Parsing              : 0.13
% 1.46/1.06  CNF conversion       : 0.01
% 1.46/1.06  Main loop            : 0.06
% 1.46/1.06  Inferencing          : 0.03
% 1.46/1.06  Reduction            : 0.02
% 1.46/1.06  Demodulation         : 0.01
% 1.46/1.06  BG Simplification    : 0.01
% 1.46/1.06  Subsumption          : 0.01
% 1.46/1.06  Abstraction          : 0.00
% 1.46/1.06  MUC search           : 0.00
% 1.46/1.06  Cooper               : 0.00
% 1.46/1.06  Total                : 0.33
% 1.46/1.06  Index Insertion      : 0.00
% 1.46/1.06  Index Deletion       : 0.00
% 1.46/1.06  Index Matching       : 0.00
% 1.46/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
