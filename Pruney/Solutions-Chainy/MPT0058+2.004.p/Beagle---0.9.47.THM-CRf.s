%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:03 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k4_xboole_0(A_5,B_6),C_7) = k4_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_120,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,B_13)) = A_12
      | ~ r1_tarski(k4_xboole_0(A_12,B_13),A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_120])).

tff(c_1952,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(k3_xboole_0(A_89,B_90),k4_xboole_0(A_89,B_90)) = A_89
      | ~ r1_tarski(k4_xboole_0(A_89,B_90),A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_18,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2084,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1952,c_18])).

tff(c_2112,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2084])).

tff(c_2116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_10,c_2112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.60  
% 3.50/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.60  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 3.50/1.60  
% 3.50/1.60  %Foreground sorts:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Background operators:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Foreground operators:
% 3.50/1.60  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.50/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.60  
% 3.50/1.61  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.50/1.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.50/1.61  tff(f_34, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.50/1.61  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.50/1.61  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.50/1.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 3.50/1.61  tff(f_45, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.50/1.61  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.50/1.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.50/1.61  tff(c_10, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k4_xboole_0(A_5, B_6), C_7)=k4_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.50/1.61  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.61  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.61  tff(c_120, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.50/1.61  tff(c_135, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, B_13))=A_12 | ~r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_120])).
% 3.50/1.61  tff(c_1952, plain, (![A_89, B_90]: (k2_xboole_0(k3_xboole_0(A_89, B_90), k4_xboole_0(A_89, B_90))=A_89 | ~r1_tarski(k4_xboole_0(A_89, B_90), A_89))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 3.50/1.61  tff(c_18, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.50/1.61  tff(c_2084, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1952, c_18])).
% 3.50/1.61  tff(c_2112, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_2084])).
% 3.50/1.61  tff(c_2116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_10, c_2112])).
% 3.50/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.61  
% 3.50/1.61  Inference rules
% 3.50/1.61  ----------------------
% 3.50/1.61  #Ref     : 0
% 3.50/1.61  #Sup     : 533
% 3.50/1.61  #Fact    : 0
% 3.50/1.61  #Define  : 0
% 3.50/1.61  #Split   : 0
% 3.50/1.61  #Chain   : 0
% 3.50/1.61  #Close   : 0
% 3.50/1.61  
% 3.50/1.61  Ordering : KBO
% 3.50/1.61  
% 3.50/1.61  Simplification rules
% 3.50/1.61  ----------------------
% 3.50/1.61  #Subsume      : 18
% 3.50/1.61  #Demod        : 243
% 3.50/1.61  #Tautology    : 298
% 3.50/1.61  #SimpNegUnit  : 0
% 3.50/1.61  #BackRed      : 1
% 3.50/1.61  
% 3.50/1.61  #Partial instantiations: 0
% 3.50/1.61  #Strategies tried      : 1
% 3.50/1.61  
% 3.50/1.61  Timing (in seconds)
% 3.50/1.61  ----------------------
% 3.50/1.62  Preprocessing        : 0.29
% 3.50/1.62  Parsing              : 0.16
% 3.50/1.62  CNF conversion       : 0.02
% 3.50/1.62  Main loop            : 0.56
% 3.50/1.62  Inferencing          : 0.19
% 3.50/1.62  Reduction            : 0.23
% 3.50/1.62  Demodulation         : 0.19
% 3.50/1.62  BG Simplification    : 0.03
% 3.50/1.62  Subsumption          : 0.08
% 3.50/1.62  Abstraction          : 0.03
% 3.50/1.62  MUC search           : 0.00
% 3.50/1.62  Cooper               : 0.00
% 3.50/1.62  Total                : 0.88
% 3.50/1.62  Index Insertion      : 0.00
% 3.50/1.62  Index Deletion       : 0.00
% 3.50/1.62  Index Matching       : 0.00
% 3.50/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
