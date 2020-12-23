%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:31 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_78])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_123,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_123])).

tff(c_150,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_141])).

tff(c_288,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k3_xboole_0(A_36,B_37),C_38) = k3_xboole_0(A_36,k4_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_327,plain,(
    ! [C_38] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_38)) = k4_xboole_0('#skF_1',C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_288])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_434,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_8])).

tff(c_469,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_434])).

tff(c_1510,plain,(
    ! [C_64] : r1_tarski(k4_xboole_0('#skF_1',C_64),k4_xboole_0('#skF_2',C_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_469])).

tff(c_1543,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1510])).

tff(c_1557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1543])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.45  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.45  
% 2.90/1.45  %Foreground sorts:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Background operators:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Foreground operators:
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.90/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.45  
% 3.05/1.46  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.05/1.46  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.05/1.46  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.05/1.46  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.05/1.46  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.05/1.46  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.05/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.05/1.46  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.05/1.46  tff(c_20, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.05/1.46  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.05/1.46  tff(c_78, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.46  tff(c_86, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_78])).
% 3.05/1.46  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.46  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.05/1.46  tff(c_95, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.46  tff(c_111, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_95])).
% 3.05/1.46  tff(c_123, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.05/1.46  tff(c_141, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_111, c_123])).
% 3.05/1.46  tff(c_150, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_141])).
% 3.05/1.46  tff(c_288, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k3_xboole_0(A_36, B_37), C_38)=k3_xboole_0(A_36, k4_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.46  tff(c_327, plain, (![C_38]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_38))=k4_xboole_0('#skF_1', C_38))), inference(superposition, [status(thm), theory('equality')], [c_150, c_288])).
% 3.05/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.05/1.46  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.05/1.46  tff(c_434, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_123, c_8])).
% 3.05/1.46  tff(c_469, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_2, c_434])).
% 3.05/1.46  tff(c_1510, plain, (![C_64]: (r1_tarski(k4_xboole_0('#skF_1', C_64), k4_xboole_0('#skF_2', C_64)))), inference(superposition, [status(thm), theory('equality')], [c_327, c_469])).
% 3.05/1.46  tff(c_1543, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1510])).
% 3.05/1.46  tff(c_1557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_1543])).
% 3.05/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.46  
% 3.05/1.46  Inference rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Ref     : 0
% 3.05/1.46  #Sup     : 391
% 3.05/1.46  #Fact    : 0
% 3.05/1.46  #Define  : 0
% 3.05/1.46  #Split   : 0
% 3.05/1.46  #Chain   : 0
% 3.05/1.46  #Close   : 0
% 3.05/1.46  
% 3.05/1.46  Ordering : KBO
% 3.05/1.46  
% 3.05/1.46  Simplification rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Subsume      : 0
% 3.05/1.46  #Demod        : 289
% 3.05/1.46  #Tautology    : 295
% 3.05/1.46  #SimpNegUnit  : 1
% 3.05/1.46  #BackRed      : 0
% 3.05/1.46  
% 3.05/1.46  #Partial instantiations: 0
% 3.05/1.46  #Strategies tried      : 1
% 3.05/1.46  
% 3.05/1.46  Timing (in seconds)
% 3.05/1.46  ----------------------
% 3.05/1.46  Preprocessing        : 0.28
% 3.05/1.46  Parsing              : 0.16
% 3.05/1.46  CNF conversion       : 0.02
% 3.05/1.46  Main loop            : 0.41
% 3.05/1.46  Inferencing          : 0.14
% 3.05/1.46  Reduction            : 0.17
% 3.05/1.46  Demodulation         : 0.14
% 3.05/1.46  BG Simplification    : 0.02
% 3.05/1.46  Subsumption          : 0.05
% 3.05/1.46  Abstraction          : 0.02
% 3.05/1.46  MUC search           : 0.00
% 3.05/1.46  Cooper               : 0.00
% 3.05/1.46  Total                : 0.72
% 3.05/1.46  Index Insertion      : 0.00
% 3.05/1.46  Index Deletion       : 0.00
% 3.05/1.46  Index Matching       : 0.00
% 3.05/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
