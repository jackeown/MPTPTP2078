%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:27 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_21,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_31,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(A_14,C_15)
      | ~ r1_tarski(B_16,C_15)
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_31])).

tff(c_8,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:21:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.07  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.56/1.07  
% 1.56/1.07  %Foreground sorts:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Background operators:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Foreground operators:
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.56/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.56/1.07  
% 1.56/1.08  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.56/1.08  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.56/1.08  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.56/1.08  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.56/1.08  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.08  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.08  tff(c_21, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4])).
% 1.56/1.08  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.08  tff(c_31, plain, (![A_14, C_15, B_16]: (r1_tarski(A_14, C_15) | ~r1_tarski(B_16, C_15) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.08  tff(c_41, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_10, c_31])).
% 1.56/1.08  tff(c_8, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.56/1.08  tff(c_46, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_41, c_8])).
% 1.56/1.08  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21, c_46])).
% 1.56/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.08  
% 1.56/1.08  Inference rules
% 1.56/1.08  ----------------------
% 1.56/1.08  #Ref     : 0
% 1.56/1.08  #Sup     : 10
% 1.56/1.08  #Fact    : 0
% 1.56/1.08  #Define  : 0
% 1.56/1.08  #Split   : 0
% 1.56/1.08  #Chain   : 0
% 1.56/1.08  #Close   : 0
% 1.56/1.08  
% 1.56/1.08  Ordering : KBO
% 1.56/1.08  
% 1.56/1.08  Simplification rules
% 1.56/1.08  ----------------------
% 1.56/1.08  #Subsume      : 0
% 1.56/1.08  #Demod        : 1
% 1.56/1.08  #Tautology    : 2
% 1.56/1.08  #SimpNegUnit  : 0
% 1.56/1.08  #BackRed      : 0
% 1.56/1.08  
% 1.56/1.08  #Partial instantiations: 0
% 1.56/1.08  #Strategies tried      : 1
% 1.56/1.08  
% 1.56/1.08  Timing (in seconds)
% 1.56/1.08  ----------------------
% 1.56/1.08  Preprocessing        : 0.24
% 1.56/1.09  Parsing              : 0.13
% 1.56/1.09  CNF conversion       : 0.01
% 1.56/1.09  Main loop            : 0.09
% 1.56/1.09  Inferencing          : 0.05
% 1.56/1.09  Reduction            : 0.02
% 1.56/1.09  Demodulation         : 0.02
% 1.56/1.09  BG Simplification    : 0.01
% 1.56/1.09  Subsumption          : 0.01
% 1.56/1.09  Abstraction          : 0.00
% 1.56/1.09  MUC search           : 0.00
% 1.56/1.09  Cooper               : 0.00
% 1.56/1.09  Total                : 0.35
% 1.56/1.09  Index Insertion      : 0.00
% 1.56/1.09  Index Deletion       : 0.00
% 1.56/1.09  Index Matching       : 0.00
% 1.56/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
