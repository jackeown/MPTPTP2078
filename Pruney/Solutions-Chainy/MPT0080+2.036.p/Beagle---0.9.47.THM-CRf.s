%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:54 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_82,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_20])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_69,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_69])).

tff(c_146,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_146])).

tff(c_166,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_161])).

tff(c_257,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(k4_xboole_0(A_33,B_34),C_35) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_718,plain,(
    ! [C_50] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_50)) = k4_xboole_0('#skF_1',C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_257])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_87,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_87])).

tff(c_737,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_95])).

tff(c_762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.42  
% 2.64/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.42  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.42  
% 2.64/1.42  %Foreground sorts:
% 2.64/1.42  
% 2.64/1.42  
% 2.64/1.42  %Background operators:
% 2.64/1.42  
% 2.64/1.42  
% 2.64/1.42  %Foreground operators:
% 2.64/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.42  
% 2.64/1.43  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.64/1.43  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.64/1.43  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.64/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.64/1.43  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.64/1.43  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.64/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.64/1.43  tff(c_82, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | k4_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.43  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.43  tff(c_86, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_20])).
% 2.64/1.43  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.43  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.43  tff(c_69, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.43  tff(c_77, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_69])).
% 2.64/1.43  tff(c_146, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.43  tff(c_161, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_146])).
% 2.64/1.43  tff(c_166, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_161])).
% 2.64/1.43  tff(c_257, plain, (![A_33, B_34, C_35]: (k4_xboole_0(k4_xboole_0(A_33, B_34), C_35)=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.43  tff(c_718, plain, (![C_50]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_50))=k4_xboole_0('#skF_1', C_50))), inference(superposition, [status(thm), theory('equality')], [c_166, c_257])).
% 2.64/1.43  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.43  tff(c_24, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.43  tff(c_25, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 2.64/1.43  tff(c_87, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.43  tff(c_95, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_87])).
% 2.64/1.43  tff(c_737, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_718, c_95])).
% 2.64/1.43  tff(c_762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_737])).
% 2.64/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  
% 2.64/1.43  Inference rules
% 2.64/1.43  ----------------------
% 2.64/1.43  #Ref     : 0
% 2.64/1.43  #Sup     : 183
% 2.64/1.43  #Fact    : 0
% 2.64/1.43  #Define  : 0
% 2.64/1.43  #Split   : 0
% 2.64/1.43  #Chain   : 0
% 2.64/1.43  #Close   : 0
% 2.64/1.43  
% 2.64/1.43  Ordering : KBO
% 2.64/1.43  
% 2.64/1.43  Simplification rules
% 2.64/1.43  ----------------------
% 2.64/1.43  #Subsume      : 0
% 2.64/1.43  #Demod        : 129
% 2.64/1.43  #Tautology    : 115
% 2.64/1.43  #SimpNegUnit  : 1
% 2.64/1.43  #BackRed      : 1
% 2.64/1.43  
% 2.64/1.43  #Partial instantiations: 0
% 2.64/1.43  #Strategies tried      : 1
% 2.64/1.43  
% 2.64/1.43  Timing (in seconds)
% 2.64/1.43  ----------------------
% 2.64/1.44  Preprocessing        : 0.28
% 2.64/1.44  Parsing              : 0.15
% 2.64/1.44  CNF conversion       : 0.02
% 2.64/1.44  Main loop            : 0.40
% 2.64/1.44  Inferencing          : 0.14
% 2.64/1.44  Reduction            : 0.16
% 2.64/1.44  Demodulation         : 0.14
% 2.64/1.44  BG Simplification    : 0.02
% 2.64/1.44  Subsumption          : 0.05
% 2.64/1.44  Abstraction          : 0.02
% 2.64/1.44  MUC search           : 0.00
% 2.64/1.44  Cooper               : 0.00
% 2.64/1.44  Total                : 0.70
% 2.64/1.44  Index Insertion      : 0.00
% 2.64/1.44  Index Deletion       : 0.00
% 2.64/1.44  Index Matching       : 0.00
% 2.64/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
