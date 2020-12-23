%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:55 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_138,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_54,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_19,c_54])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_311,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_xboole_0 = A_34
      | ~ r1_xboole_0(B_35,C_36)
      | ~ r1_tarski(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_368,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,'#skF_3')
      | ~ r1_tarski(A_39,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_311])).

tff(c_1059,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ r1_tarski(A_64,'#skF_1')
      | k4_xboole_0(A_64,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_368])).

tff(c_1071,plain,(
    ! [B_6] :
      ( k4_xboole_0('#skF_1',B_6) = k1_xboole_0
      | k4_xboole_0(k4_xboole_0('#skF_1',B_6),'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1059])).

tff(c_2874,plain,(
    ! [B_97] :
      ( k4_xboole_0('#skF_1',B_97) = k1_xboole_0
      | k4_xboole_0('#skF_1',k2_xboole_0(B_97,'#skF_3')) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1071])).

tff(c_4284,plain,(
    ! [A_114] :
      ( k4_xboole_0('#skF_1',A_114) = k1_xboole_0
      | k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',A_114)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2874])).

tff(c_4317,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_4284])).

tff(c_4341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_4317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.87  
% 4.69/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.87  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.69/1.87  
% 4.69/1.87  %Foreground sorts:
% 4.69/1.87  
% 4.69/1.87  
% 4.69/1.87  %Background operators:
% 4.69/1.87  
% 4.69/1.87  
% 4.69/1.87  %Foreground operators:
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.69/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.69/1.87  
% 4.69/1.88  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.69/1.88  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.69/1.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.69/1.88  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.69/1.88  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.69/1.88  tff(f_43, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 4.69/1.88  tff(c_138, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | k4_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.88  tff(c_14, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.69/1.88  tff(c_146, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_14])).
% 4.69/1.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.69/1.88  tff(c_18, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.69/1.88  tff(c_19, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 4.69/1.88  tff(c_54, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.88  tff(c_62, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_19, c_54])).
% 4.69/1.88  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.69/1.88  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.69/1.88  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.88  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.69/1.88  tff(c_311, plain, (![A_34, B_35, C_36]: (k1_xboole_0=A_34 | ~r1_xboole_0(B_35, C_36) | ~r1_tarski(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.69/1.88  tff(c_368, plain, (![A_39]: (k1_xboole_0=A_39 | ~r1_tarski(A_39, '#skF_3') | ~r1_tarski(A_39, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_311])).
% 4.69/1.88  tff(c_1059, plain, (![A_64]: (k1_xboole_0=A_64 | ~r1_tarski(A_64, '#skF_1') | k4_xboole_0(A_64, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_368])).
% 4.69/1.88  tff(c_1071, plain, (![B_6]: (k4_xboole_0('#skF_1', B_6)=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', B_6), '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1059])).
% 4.69/1.88  tff(c_2874, plain, (![B_97]: (k4_xboole_0('#skF_1', B_97)=k1_xboole_0 | k4_xboole_0('#skF_1', k2_xboole_0(B_97, '#skF_3'))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1071])).
% 4.69/1.88  tff(c_4284, plain, (![A_114]: (k4_xboole_0('#skF_1', A_114)=k1_xboole_0 | k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', A_114))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2874])).
% 4.69/1.88  tff(c_4317, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_62, c_4284])).
% 4.69/1.88  tff(c_4341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_4317])).
% 4.69/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.88  
% 4.69/1.88  Inference rules
% 4.69/1.88  ----------------------
% 4.69/1.88  #Ref     : 0
% 4.69/1.88  #Sup     : 1081
% 4.69/1.88  #Fact    : 0
% 4.69/1.88  #Define  : 0
% 4.69/1.88  #Split   : 1
% 4.69/1.88  #Chain   : 0
% 4.69/1.88  #Close   : 0
% 4.69/1.88  
% 4.69/1.88  Ordering : KBO
% 4.69/1.88  
% 4.69/1.88  Simplification rules
% 4.69/1.88  ----------------------
% 4.69/1.88  #Subsume      : 5
% 4.69/1.88  #Demod        : 792
% 4.69/1.88  #Tautology    : 719
% 4.69/1.88  #SimpNegUnit  : 1
% 4.69/1.88  #BackRed      : 4
% 4.69/1.88  
% 4.69/1.88  #Partial instantiations: 0
% 4.69/1.88  #Strategies tried      : 1
% 4.69/1.88  
% 4.69/1.88  Timing (in seconds)
% 4.69/1.88  ----------------------
% 4.69/1.88  Preprocessing        : 0.28
% 4.69/1.88  Parsing              : 0.16
% 4.69/1.88  CNF conversion       : 0.02
% 4.69/1.89  Main loop            : 0.87
% 4.69/1.89  Inferencing          : 0.24
% 4.69/1.89  Reduction            : 0.43
% 4.69/1.89  Demodulation         : 0.36
% 4.69/1.89  BG Simplification    : 0.03
% 4.69/1.89  Subsumption          : 0.13
% 4.69/1.89  Abstraction          : 0.03
% 4.69/1.89  MUC search           : 0.00
% 4.69/1.89  Cooper               : 0.00
% 4.69/1.89  Total                : 1.17
% 4.69/1.89  Index Insertion      : 0.00
% 4.69/1.89  Index Deletion       : 0.00
% 4.69/1.89  Index Matching       : 0.00
% 4.69/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
