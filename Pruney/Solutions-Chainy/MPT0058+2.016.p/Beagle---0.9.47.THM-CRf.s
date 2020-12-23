%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:04 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5
      | ~ r1_tarski(k3_xboole_0(A_5,B_6),A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_19])).

tff(c_32,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_8,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:12:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.37  
% 1.77/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.38  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.77/1.38  
% 1.77/1.38  %Foreground sorts:
% 1.77/1.38  
% 1.77/1.38  
% 1.77/1.38  %Background operators:
% 1.77/1.38  
% 1.77/1.38  
% 1.77/1.38  %Foreground operators:
% 1.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.38  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.38  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.38  
% 1.77/1.39  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.77/1.39  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.77/1.39  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.77/1.39  tff(f_36, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.77/1.39  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.39  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.39  tff(c_19, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.39  tff(c_28, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5 | ~r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_19])).
% 1.77/1.39  tff(c_32, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 1.77/1.39  tff(c_8, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.77/1.39  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 1.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.39  
% 1.77/1.39  Inference rules
% 1.77/1.39  ----------------------
% 1.77/1.39  #Ref     : 0
% 1.77/1.39  #Sup     : 5
% 1.77/1.39  #Fact    : 0
% 1.77/1.39  #Define  : 0
% 1.77/1.39  #Split   : 0
% 1.77/1.39  #Chain   : 0
% 1.77/1.39  #Close   : 0
% 1.77/1.39  
% 1.77/1.39  Ordering : KBO
% 1.77/1.39  
% 1.77/1.39  Simplification rules
% 1.77/1.39  ----------------------
% 1.77/1.39  #Subsume      : 0
% 1.77/1.39  #Demod        : 2
% 1.77/1.39  #Tautology    : 4
% 1.77/1.39  #SimpNegUnit  : 0
% 1.77/1.39  #BackRed      : 1
% 1.77/1.39  
% 1.77/1.39  #Partial instantiations: 0
% 1.77/1.39  #Strategies tried      : 1
% 1.77/1.39  
% 1.77/1.39  Timing (in seconds)
% 1.77/1.39  ----------------------
% 1.77/1.40  Preprocessing        : 0.36
% 1.77/1.40  Parsing              : 0.20
% 1.77/1.40  CNF conversion       : 0.02
% 1.77/1.40  Main loop            : 0.11
% 1.77/1.40  Inferencing          : 0.05
% 1.77/1.40  Reduction            : 0.03
% 1.77/1.40  Demodulation         : 0.03
% 1.77/1.40  BG Simplification    : 0.01
% 1.77/1.40  Subsumption          : 0.01
% 1.77/1.40  Abstraction          : 0.01
% 1.77/1.40  MUC search           : 0.00
% 1.77/1.40  Cooper               : 0.00
% 1.77/1.40  Total                : 0.52
% 1.77/1.40  Index Insertion      : 0.00
% 1.77/1.40  Index Deletion       : 0.00
% 1.77/1.40  Index Matching       : 0.00
% 1.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
