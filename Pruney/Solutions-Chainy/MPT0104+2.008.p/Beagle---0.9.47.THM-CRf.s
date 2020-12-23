%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_25,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_29,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25,c_18])).

tff(c_10,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_22,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_30])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),k3_xboole_0(A_13,B_14)) = k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(B_14,A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(A_13,B_14),k4_xboole_0(B_14,A_13)) = k5_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_20,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_278,plain,(
    ! [A_35,C_36,B_37] : k2_xboole_0(k4_xboole_0(A_35,C_36),k4_xboole_0(B_37,C_36)) = k4_xboole_0(k2_xboole_0(A_35,B_37),C_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_729,plain,(
    ! [A_47] : k4_xboole_0(k2_xboole_0(A_47,k4_xboole_0('#skF_2','#skF_1')),'#skF_3') = k2_xboole_0(k4_xboole_0(A_47,'#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_278])).

tff(c_776,plain,(
    k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3'),k1_xboole_0) = k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_23,c_729])).

tff(c_787,plain,(
    k4_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_44,c_776])).

tff(c_789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.73  
% 2.89/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.74  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.74  
% 2.89/1.74  %Foreground sorts:
% 2.89/1.74  
% 2.89/1.74  
% 2.89/1.74  %Background operators:
% 2.89/1.74  
% 2.89/1.74  
% 2.89/1.74  %Foreground operators:
% 2.89/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.74  
% 2.89/1.74  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.89/1.74  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 2.89/1.74  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.89/1.74  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.89/1.74  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.89/1.74  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 2.89/1.74  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 2.89/1.74  tff(c_25, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.74  tff(c_18, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.74  tff(c_29, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_25, c_18])).
% 2.89/1.74  tff(c_10, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.74  tff(c_62, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.74  tff(c_78, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_10, c_62])).
% 2.89/1.74  tff(c_22, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.75  tff(c_30, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.75  tff(c_44, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_30])).
% 2.89/1.75  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.75  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), k3_xboole_0(A_13, B_14))=k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(B_14, A_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.75  tff(c_23, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(A_13, B_14), k4_xboole_0(B_14, A_13))=k5_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.89/1.75  tff(c_20, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.75  tff(c_45, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_30])).
% 2.89/1.75  tff(c_278, plain, (![A_35, C_36, B_37]: (k2_xboole_0(k4_xboole_0(A_35, C_36), k4_xboole_0(B_37, C_36))=k4_xboole_0(k2_xboole_0(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.75  tff(c_729, plain, (![A_47]: (k4_xboole_0(k2_xboole_0(A_47, k4_xboole_0('#skF_2', '#skF_1')), '#skF_3')=k2_xboole_0(k4_xboole_0(A_47, '#skF_3'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_45, c_278])).
% 2.89/1.75  tff(c_776, plain, (k2_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3'), k1_xboole_0)=k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_23, c_729])).
% 2.89/1.75  tff(c_787, plain, (k4_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_44, c_776])).
% 2.89/1.75  tff(c_789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_787])).
% 2.89/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.75  
% 2.89/1.75  Inference rules
% 2.89/1.75  ----------------------
% 2.89/1.75  #Ref     : 0
% 2.89/1.75  #Sup     : 206
% 2.89/1.75  #Fact    : 0
% 2.89/1.75  #Define  : 0
% 2.89/1.75  #Split   : 0
% 2.89/1.75  #Chain   : 0
% 2.89/1.75  #Close   : 0
% 2.89/1.75  
% 2.89/1.75  Ordering : KBO
% 2.89/1.75  
% 2.89/1.75  Simplification rules
% 2.89/1.75  ----------------------
% 2.89/1.75  #Subsume      : 0
% 2.89/1.75  #Demod        : 126
% 2.89/1.75  #Tautology    : 84
% 2.89/1.75  #SimpNegUnit  : 1
% 2.89/1.75  #BackRed      : 0
% 2.89/1.75  
% 2.89/1.75  #Partial instantiations: 0
% 2.89/1.75  #Strategies tried      : 1
% 2.89/1.75  
% 2.89/1.75  Timing (in seconds)
% 2.89/1.75  ----------------------
% 2.89/1.75  Preprocessing        : 0.46
% 2.89/1.75  Parsing              : 0.24
% 2.89/1.75  CNF conversion       : 0.03
% 2.89/1.75  Main loop            : 0.47
% 2.89/1.75  Inferencing          : 0.17
% 2.89/1.75  Reduction            : 0.18
% 2.89/1.75  Demodulation         : 0.14
% 2.89/1.75  BG Simplification    : 0.03
% 2.89/1.75  Subsumption          : 0.07
% 2.89/1.75  Abstraction          : 0.03
% 2.89/1.75  MUC search           : 0.00
% 2.89/1.75  Cooper               : 0.00
% 2.89/1.75  Total                : 0.96
% 2.89/1.75  Index Insertion      : 0.00
% 2.89/1.75  Index Deletion       : 0.00
% 2.89/1.75  Index Matching       : 0.00
% 2.89/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
