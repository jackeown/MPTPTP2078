%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:30 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_21,A_22,B_23] :
      ( r1_tarski(A_21,k2_xboole_0(A_22,B_23))
      | ~ r1_tarski(A_21,A_22) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_86,plain,(
    ! [A_21,B_2,A_1] :
      ( r1_tarski(A_21,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_21,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_78])).

tff(c_110,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(k2_xboole_0(A_27,C_28),B_29)
      | ~ r1_tarski(C_28,B_29)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_13,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_124,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_110,c_13])).

tff(c_139,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_146,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_139])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.66/1.14  
% 1.66/1.14  %Foreground sorts:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Background operators:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Foreground operators:
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.14  
% 1.82/1.15  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 1.82/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.82/1.15  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.82/1.15  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.82/1.15  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.82/1.15  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.15  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.15  tff(c_64, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.15  tff(c_78, plain, (![A_21, A_22, B_23]: (r1_tarski(A_21, k2_xboole_0(A_22, B_23)) | ~r1_tarski(A_21, A_22))), inference(resolution, [status(thm)], [c_6, c_64])).
% 1.82/1.15  tff(c_86, plain, (![A_21, B_2, A_1]: (r1_tarski(A_21, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_21, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_78])).
% 1.82/1.15  tff(c_110, plain, (![A_27, C_28, B_29]: (r1_tarski(k2_xboole_0(A_27, C_28), B_29) | ~r1_tarski(C_28, B_29) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.15  tff(c_10, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.15  tff(c_13, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.82/1.15  tff(c_124, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_110, c_13])).
% 1.82/1.15  tff(c_139, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_124])).
% 1.82/1.15  tff(c_146, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_139])).
% 1.82/1.15  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_146])).
% 1.82/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  Inference rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Ref     : 0
% 1.82/1.15  #Sup     : 35
% 1.82/1.15  #Fact    : 0
% 1.82/1.15  #Define  : 0
% 1.82/1.15  #Split   : 0
% 1.82/1.15  #Chain   : 0
% 1.82/1.15  #Close   : 0
% 1.82/1.15  
% 1.82/1.15  Ordering : KBO
% 1.82/1.15  
% 1.82/1.15  Simplification rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Subsume      : 6
% 1.82/1.15  #Demod        : 7
% 1.82/1.15  #Tautology    : 11
% 1.82/1.15  #SimpNegUnit  : 0
% 1.82/1.15  #BackRed      : 0
% 1.82/1.15  
% 1.82/1.15  #Partial instantiations: 0
% 1.82/1.15  #Strategies tried      : 1
% 1.82/1.15  
% 1.82/1.15  Timing (in seconds)
% 1.82/1.15  ----------------------
% 1.82/1.15  Preprocessing        : 0.25
% 1.82/1.15  Parsing              : 0.14
% 1.82/1.15  CNF conversion       : 0.01
% 1.82/1.15  Main loop            : 0.15
% 1.82/1.15  Inferencing          : 0.05
% 1.82/1.15  Reduction            : 0.06
% 1.82/1.15  Demodulation         : 0.05
% 1.82/1.15  BG Simplification    : 0.01
% 1.82/1.15  Subsumption          : 0.03
% 1.82/1.15  Abstraction          : 0.01
% 1.82/1.15  MUC search           : 0.00
% 1.82/1.15  Cooper               : 0.00
% 1.82/1.15  Total                : 0.42
% 1.82/1.15  Index Insertion      : 0.00
% 1.82/1.15  Index Deletion       : 0.00
% 1.82/1.15  Index Matching       : 0.00
% 1.82/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
