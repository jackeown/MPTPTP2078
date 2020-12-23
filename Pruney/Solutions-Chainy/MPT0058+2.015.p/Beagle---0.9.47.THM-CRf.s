%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:04 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  28 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_118,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_14])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(k4_xboole_0(A_21,B_22),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_6])).

tff(c_84,plain,(
    ! [A_21,B_22] : k2_xboole_0(k4_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_124,plain,(
    ! [A_29,B_30] : k2_xboole_0(k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_84])).

tff(c_144,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_12,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:00:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.13  
% 1.67/1.14  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.67/1.14  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.67/1.14  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.67/1.14  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.67/1.14  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.67/1.14  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.67/1.14  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.14  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.14  tff(c_57, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.14  tff(c_75, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 1.67/1.14  tff(c_118, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_75])).
% 1.67/1.14  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.14  tff(c_18, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_14])).
% 1.67/1.14  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.14  tff(c_66, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(k4_xboole_0(A_21, B_22), A_21))), inference(superposition, [status(thm), theory('equality')], [c_57, c_6])).
% 1.67/1.14  tff(c_84, plain, (![A_21, B_22]: (k2_xboole_0(k4_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 1.67/1.14  tff(c_124, plain, (![A_29, B_30]: (k2_xboole_0(k4_xboole_0(A_29, k4_xboole_0(A_29, B_30)), k4_xboole_0(A_29, B_30))=A_29)), inference(superposition, [status(thm), theory('equality')], [c_118, c_84])).
% 1.67/1.14  tff(c_144, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_124])).
% 1.67/1.14  tff(c_12, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.14  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_12])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 42
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 29
% 1.67/1.14  #Tautology    : 31
% 1.67/1.14  #SimpNegUnit  : 0
% 1.67/1.14  #BackRed      : 1
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.14  Preprocessing        : 0.25
% 1.67/1.14  Parsing              : 0.14
% 1.67/1.14  CNF conversion       : 0.01
% 1.67/1.14  Main loop            : 0.14
% 1.67/1.14  Inferencing          : 0.06
% 1.67/1.14  Reduction            : 0.05
% 1.67/1.14  Demodulation         : 0.04
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.02
% 1.67/1.14  Abstraction          : 0.01
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.14  Total                : 0.42
% 1.67/1.14  Index Insertion      : 0.00
% 1.67/1.14  Index Deletion       : 0.00
% 1.67/1.14  Index Matching       : 0.00
% 1.67/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
