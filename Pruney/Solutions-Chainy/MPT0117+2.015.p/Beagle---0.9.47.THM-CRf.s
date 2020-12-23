%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  68 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_27,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_27])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,'#skF_2')
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(k2_xboole_0(A_52,C_53),B_54)
      | ~ r1_tarski(C_53,B_54)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_474,plain,(
    ! [A_97,B_98,B_99] :
      ( r1_tarski(k5_xboole_0(A_97,B_98),B_99)
      | ~ r1_tarski(k4_xboole_0(B_98,A_97),B_99)
      | ~ r1_tarski(k4_xboole_0(A_97,B_98),B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_12,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_536,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_474,c_12])).

tff(c_537,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_546,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_537])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_546])).

tff(c_556,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_569,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_35,c_556])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:41:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.45/1.35  
% 2.45/1.35  %Foreground sorts:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Background operators:
% 2.45/1.35  
% 2.45/1.35  
% 2.45/1.35  %Foreground operators:
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.45/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.35  
% 2.45/1.36  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.45/1.36  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.45/1.36  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.45/1.36  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.45/1.36  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.45/1.36  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.36  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.36  tff(c_27, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.36  tff(c_35, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_27])).
% 2.45/1.36  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.36  tff(c_36, plain, (![A_17]: (r1_tarski(A_17, '#skF_2') | ~r1_tarski(A_17, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_27])).
% 2.45/1.36  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.45/1.36  tff(c_191, plain, (![A_52, C_53, B_54]: (r1_tarski(k2_xboole_0(A_52, C_53), B_54) | ~r1_tarski(C_53, B_54) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.36  tff(c_474, plain, (![A_97, B_98, B_99]: (r1_tarski(k5_xboole_0(A_97, B_98), B_99) | ~r1_tarski(k4_xboole_0(B_98, A_97), B_99) | ~r1_tarski(k4_xboole_0(A_97, B_98), B_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 2.45/1.36  tff(c_12, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.36  tff(c_536, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_474, c_12])).
% 2.45/1.36  tff(c_537, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_536])).
% 2.45/1.36  tff(c_546, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_36, c_537])).
% 2.45/1.36  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_546])).
% 2.45/1.36  tff(c_556, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_536])).
% 2.45/1.36  tff(c_569, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_35, c_556])).
% 2.45/1.36  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_569])).
% 2.45/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  Inference rules
% 2.45/1.36  ----------------------
% 2.45/1.36  #Ref     : 0
% 2.45/1.36  #Sup     : 131
% 2.45/1.36  #Fact    : 0
% 2.45/1.36  #Define  : 0
% 2.45/1.36  #Split   : 1
% 2.45/1.36  #Chain   : 0
% 2.45/1.37  #Close   : 0
% 2.45/1.37  
% 2.45/1.37  Ordering : KBO
% 2.45/1.37  
% 2.45/1.37  Simplification rules
% 2.45/1.37  ----------------------
% 2.45/1.37  #Subsume      : 22
% 2.45/1.37  #Demod        : 11
% 2.45/1.37  #Tautology    : 11
% 2.45/1.37  #SimpNegUnit  : 0
% 2.45/1.37  #BackRed      : 0
% 2.45/1.37  
% 2.45/1.37  #Partial instantiations: 0
% 2.45/1.37  #Strategies tried      : 1
% 2.45/1.37  
% 2.45/1.37  Timing (in seconds)
% 2.45/1.37  ----------------------
% 2.45/1.37  Preprocessing        : 0.26
% 2.45/1.37  Parsing              : 0.15
% 2.45/1.37  CNF conversion       : 0.02
% 2.45/1.37  Main loop            : 0.34
% 2.45/1.37  Inferencing          : 0.14
% 2.45/1.37  Reduction            : 0.09
% 2.45/1.37  Demodulation         : 0.07
% 2.45/1.37  BG Simplification    : 0.01
% 2.45/1.37  Subsumption          : 0.08
% 2.45/1.37  Abstraction          : 0.01
% 2.45/1.37  MUC search           : 0.00
% 2.45/1.37  Cooper               : 0.00
% 2.45/1.37  Total                : 0.63
% 2.45/1.37  Index Insertion      : 0.00
% 2.45/1.37  Index Deletion       : 0.00
% 2.45/1.37  Index Matching       : 0.00
% 2.45/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
