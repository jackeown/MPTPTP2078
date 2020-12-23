%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_20,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_45])).

tff(c_12,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_31])).

tff(c_58,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_58])).

tff(c_79,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_12,c_73])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_87,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_6])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.37  
% 1.90/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.37  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.90/1.37  
% 1.90/1.37  %Foreground sorts:
% 1.90/1.37  
% 1.90/1.37  
% 1.90/1.37  %Background operators:
% 1.90/1.37  
% 1.90/1.37  
% 1.90/1.37  %Foreground operators:
% 1.90/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.37  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.37  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.37  
% 1.90/1.38  tff(f_47, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.90/1.38  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.90/1.38  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.90/1.38  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.90/1.38  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.90/1.38  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.38  tff(c_20, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.38  tff(c_16, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.38  tff(c_45, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.38  tff(c_53, plain, (k3_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_45])).
% 1.90/1.38  tff(c_12, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.38  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.38  tff(c_31, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.38  tff(c_39, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_31])).
% 1.90/1.38  tff(c_58, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.38  tff(c_73, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39, c_58])).
% 1.90/1.38  tff(c_79, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_12, c_73])).
% 1.90/1.38  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.90/1.38  tff(c_87, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_6])).
% 1.90/1.38  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_87])).
% 1.90/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.38  
% 1.90/1.38  Inference rules
% 1.90/1.38  ----------------------
% 1.90/1.38  #Ref     : 0
% 1.90/1.38  #Sup     : 16
% 1.90/1.38  #Fact    : 0
% 1.90/1.38  #Define  : 0
% 1.90/1.38  #Split   : 0
% 1.90/1.38  #Chain   : 0
% 1.90/1.38  #Close   : 0
% 1.90/1.38  
% 1.90/1.38  Ordering : KBO
% 1.90/1.38  
% 1.90/1.38  Simplification rules
% 1.90/1.38  ----------------------
% 1.90/1.38  #Subsume      : 0
% 1.90/1.38  #Demod        : 10
% 1.90/1.38  #Tautology    : 10
% 1.90/1.38  #SimpNegUnit  : 1
% 1.90/1.38  #BackRed      : 8
% 1.90/1.38  
% 1.90/1.38  #Partial instantiations: 0
% 1.90/1.38  #Strategies tried      : 1
% 1.90/1.38  
% 1.90/1.38  Timing (in seconds)
% 1.90/1.38  ----------------------
% 1.90/1.39  Preprocessing        : 0.33
% 1.90/1.39  Parsing              : 0.19
% 1.90/1.39  CNF conversion       : 0.02
% 1.90/1.39  Main loop            : 0.13
% 1.90/1.39  Inferencing          : 0.06
% 1.90/1.39  Reduction            : 0.04
% 1.90/1.39  Demodulation         : 0.03
% 1.90/1.39  BG Simplification    : 0.01
% 1.90/1.39  Subsumption          : 0.02
% 1.90/1.39  Abstraction          : 0.01
% 1.90/1.39  MUC search           : 0.00
% 1.90/1.39  Cooper               : 0.00
% 1.90/1.39  Total                : 0.49
% 1.90/1.39  Index Insertion      : 0.00
% 1.90/1.39  Index Deletion       : 0.00
% 1.90/1.39  Index Matching       : 0.00
% 1.90/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
