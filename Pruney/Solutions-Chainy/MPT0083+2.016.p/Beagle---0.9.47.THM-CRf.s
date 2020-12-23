%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  55 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_58,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_6])).

tff(c_79,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_xboole_0(A_24,C_25)
      | ~ r1_xboole_0(B_26,C_25)
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    ! [A_27] :
      ( r1_xboole_0(A_27,'#skF_2')
      | ~ r1_tarski(A_27,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_92])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_29] :
      ( r1_xboole_0('#skF_2',A_29)
      | ~ r1_tarski(A_29,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_239,plain,(
    ! [A_47,A_48] :
      ( r1_xboole_0(A_47,A_48)
      | ~ r1_tarski(A_47,'#skF_2')
      | ~ r1_tarski(A_48,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_372,plain,(
    ! [A_63,A_64] :
      ( r1_xboole_0(A_63,A_64)
      | ~ r1_tarski(A_64,'#skF_2')
      | ~ r1_tarski(A_63,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_239,c_4])).

tff(c_12,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_377,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_372,c_15])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_79,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:43:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.30  
% 2.12/1.31  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.12/1.31  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.12/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.12/1.31  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.12/1.31  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.12/1.31  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.12/1.31  tff(c_58, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.31  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_67, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_58, c_6])).
% 2.12/1.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.31  tff(c_76, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_58, c_6])).
% 2.12/1.31  tff(c_79, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_76])).
% 2.12/1.31  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.31  tff(c_92, plain, (![A_24, C_25, B_26]: (r1_xboole_0(A_24, C_25) | ~r1_xboole_0(B_26, C_25) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.31  tff(c_100, plain, (![A_27]: (r1_xboole_0(A_27, '#skF_2') | ~r1_tarski(A_27, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_92])).
% 2.12/1.31  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.31  tff(c_114, plain, (![A_29]: (r1_xboole_0('#skF_2', A_29) | ~r1_tarski(A_29, '#skF_1'))), inference(resolution, [status(thm)], [c_100, c_4])).
% 2.12/1.31  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_xboole_0(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.31  tff(c_239, plain, (![A_47, A_48]: (r1_xboole_0(A_47, A_48) | ~r1_tarski(A_47, '#skF_2') | ~r1_tarski(A_48, '#skF_1'))), inference(resolution, [status(thm)], [c_114, c_10])).
% 2.12/1.31  tff(c_372, plain, (![A_63, A_64]: (r1_xboole_0(A_63, A_64) | ~r1_tarski(A_64, '#skF_2') | ~r1_tarski(A_63, '#skF_1'))), inference(resolution, [status(thm)], [c_239, c_4])).
% 2.12/1.31  tff(c_12, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.31  tff(c_15, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.12/1.31  tff(c_377, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_372, c_15])).
% 2.12/1.31  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_79, c_377])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 103
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 1
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 30
% 2.12/1.31  #Demod        : 12
% 2.12/1.31  #Tautology    : 25
% 2.12/1.31  #SimpNegUnit  : 0
% 2.12/1.31  #BackRed      : 0
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.32  Preprocessing        : 0.26
% 2.12/1.32  Parsing              : 0.15
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.28
% 2.12/1.32  Inferencing          : 0.09
% 2.12/1.32  Reduction            : 0.09
% 2.12/1.32  Demodulation         : 0.07
% 2.12/1.32  BG Simplification    : 0.01
% 2.12/1.32  Subsumption          : 0.06
% 2.12/1.32  Abstraction          : 0.01
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.57
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
