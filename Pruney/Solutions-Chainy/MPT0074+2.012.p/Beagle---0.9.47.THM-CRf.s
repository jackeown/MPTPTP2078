%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:28 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_89,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_89])).

tff(c_114,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_143,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_xboole_0(A_27,C_28)
      | ~ r1_xboole_0(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [A_30] :
      ( r1_xboole_0(A_30,'#skF_3')
      | ~ r1_tarski(A_30,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_213,plain,(
    ! [A_36] :
      ( k3_xboole_0(A_36,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_36,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_220,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_213])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_220])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:03:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.36  
% 2.08/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.36  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.08/1.36  
% 2.08/1.36  %Foreground sorts:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Background operators:
% 2.08/1.36  
% 2.08/1.36  
% 2.08/1.36  %Foreground operators:
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.36  
% 2.08/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.08/1.37  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.08/1.37  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.08/1.37  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.08/1.37  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.08/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.08/1.37  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.37  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.37  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.37  tff(c_42, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.37  tff(c_49, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_42])).
% 2.08/1.37  tff(c_89, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.37  tff(c_107, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_49, c_89])).
% 2.08/1.37  tff(c_114, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_107])).
% 2.08/1.37  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.37  tff(c_20, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.37  tff(c_143, plain, (![A_27, C_28, B_29]: (r1_xboole_0(A_27, C_28) | ~r1_xboole_0(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.37  tff(c_158, plain, (![A_30]: (r1_xboole_0(A_30, '#skF_3') | ~r1_tarski(A_30, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_143])).
% 2.08/1.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.37  tff(c_213, plain, (![A_36]: (k3_xboole_0(A_36, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_36, '#skF_2'))), inference(resolution, [status(thm)], [c_158, c_2])).
% 2.08/1.37  tff(c_220, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_213])).
% 2.08/1.37  tff(c_223, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_220])).
% 2.08/1.37  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_223])).
% 2.08/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.37  
% 2.08/1.37  Inference rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Ref     : 0
% 2.08/1.37  #Sup     : 57
% 2.08/1.37  #Fact    : 0
% 2.08/1.37  #Define  : 0
% 2.08/1.37  #Split   : 0
% 2.08/1.37  #Chain   : 0
% 2.08/1.37  #Close   : 0
% 2.08/1.37  
% 2.08/1.37  Ordering : KBO
% 2.08/1.37  
% 2.08/1.37  Simplification rules
% 2.08/1.37  ----------------------
% 2.08/1.37  #Subsume      : 3
% 2.08/1.37  #Demod        : 5
% 2.08/1.37  #Tautology    : 24
% 2.08/1.37  #SimpNegUnit  : 1
% 2.08/1.37  #BackRed      : 0
% 2.08/1.37  
% 2.08/1.37  #Partial instantiations: 0
% 2.08/1.37  #Strategies tried      : 1
% 2.08/1.37  
% 2.08/1.37  Timing (in seconds)
% 2.08/1.37  ----------------------
% 2.08/1.37  Preprocessing        : 0.38
% 2.08/1.37  Parsing              : 0.17
% 2.08/1.37  CNF conversion       : 0.03
% 2.08/1.37  Main loop            : 0.19
% 2.08/1.37  Inferencing          : 0.08
% 2.08/1.37  Reduction            : 0.05
% 2.08/1.37  Demodulation         : 0.04
% 2.08/1.37  BG Simplification    : 0.02
% 2.08/1.37  Subsumption          : 0.04
% 2.08/1.37  Abstraction          : 0.01
% 2.08/1.37  MUC search           : 0.00
% 2.08/1.37  Cooper               : 0.00
% 2.08/1.37  Total                : 0.61
% 2.08/1.37  Index Insertion      : 0.00
% 2.08/1.37  Index Deletion       : 0.00
% 2.08/1.38  Index Matching       : 0.00
% 2.08/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
