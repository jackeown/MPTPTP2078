%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:04 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   10 (  10 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_21,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5
      | ~ r1_tarski(k3_xboole_0(A_5,B_6),A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_48])).

tff(c_64,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k4_xboole_0(A_5,B_6)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_57])).

tff(c_10,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.17  
% 1.71/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.17  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.71/1.17  
% 1.71/1.17  %Foreground sorts:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Background operators:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Foreground operators:
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.17  
% 1.71/1.18  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.71/1.18  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.71/1.18  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.71/1.18  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.71/1.18  tff(f_38, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.71/1.18  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.18  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.18  tff(c_21, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2])).
% 1.71/1.18  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.18  tff(c_48, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.18  tff(c_57, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5 | ~r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_48])).
% 1.71/1.18  tff(c_64, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k4_xboole_0(A_5, B_6))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_21, c_57])).
% 1.71/1.18  tff(c_10, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.18  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_10])).
% 1.71/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  Inference rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Ref     : 0
% 1.71/1.18  #Sup     : 24
% 1.71/1.18  #Fact    : 0
% 1.71/1.18  #Define  : 0
% 1.71/1.18  #Split   : 0
% 1.71/1.18  #Chain   : 0
% 1.71/1.18  #Close   : 0
% 1.71/1.18  
% 1.71/1.18  Ordering : KBO
% 1.71/1.18  
% 1.71/1.18  Simplification rules
% 1.71/1.18  ----------------------
% 1.71/1.18  #Subsume      : 0
% 1.71/1.18  #Demod        : 16
% 1.71/1.18  #Tautology    : 17
% 1.71/1.18  #SimpNegUnit  : 0
% 1.71/1.18  #BackRed      : 1
% 1.71/1.18  
% 1.71/1.18  #Partial instantiations: 0
% 1.71/1.18  #Strategies tried      : 1
% 1.71/1.18  
% 1.71/1.18  Timing (in seconds)
% 1.71/1.18  ----------------------
% 1.71/1.18  Preprocessing        : 0.25
% 1.71/1.18  Parsing              : 0.14
% 1.71/1.18  CNF conversion       : 0.01
% 1.71/1.18  Main loop            : 0.10
% 1.71/1.18  Inferencing          : 0.05
% 1.71/1.18  Reduction            : 0.03
% 1.71/1.19  Demodulation         : 0.03
% 1.71/1.19  BG Simplification    : 0.01
% 1.71/1.19  Subsumption          : 0.01
% 1.71/1.19  Abstraction          : 0.01
% 1.71/1.19  MUC search           : 0.00
% 1.71/1.19  Cooper               : 0.00
% 1.71/1.19  Total                : 0.38
% 1.71/1.19  Index Insertion      : 0.00
% 1.71/1.19  Index Deletion       : 0.00
% 1.71/1.19  Index Matching       : 0.00
% 1.71/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
