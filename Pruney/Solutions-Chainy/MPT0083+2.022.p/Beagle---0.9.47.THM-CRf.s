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
% DateTime   : Thu Dec  3 09:44:04 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   28 (  35 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   28 (  36 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_48,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_73,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [A_17,C_18,B_19,D_20] :
      ( r1_xboole_0(A_17,C_18)
      | ~ r1_xboole_0(B_19,D_20)
      | ~ r1_tarski(C_18,D_20)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_25,C_26] :
      ( r1_xboole_0(A_25,C_26)
      | ~ r1_tarski(C_26,'#skF_2')
      | ~ r1_tarski(A_25,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_10,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_92,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_13])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_73,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.13  
% 1.64/1.14  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.64/1.14  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.64/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.64/1.14  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 1.64/1.14  tff(f_39, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.64/1.14  tff(c_48, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.14  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.14  tff(c_57, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4])).
% 1.64/1.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.14  tff(c_70, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4])).
% 1.64/1.14  tff(c_73, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_70])).
% 1.64/1.14  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.14  tff(c_66, plain, (![A_17, C_18, B_19, D_20]: (r1_xboole_0(A_17, C_18) | ~r1_xboole_0(B_19, D_20) | ~r1_tarski(C_18, D_20) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.14  tff(c_87, plain, (![A_25, C_26]: (r1_xboole_0(A_25, C_26) | ~r1_tarski(C_26, '#skF_2') | ~r1_tarski(A_25, '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_66])).
% 1.64/1.14  tff(c_10, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.64/1.14  tff(c_13, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.64/1.14  tff(c_92, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_87, c_13])).
% 1.64/1.14  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_73, c_92])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 20
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 0
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.14  
% 1.64/1.14  Ordering : KBO
% 1.64/1.14  
% 1.64/1.14  Simplification rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Subsume      : 0
% 1.64/1.14  #Demod        : 6
% 1.64/1.14  #Tautology    : 13
% 1.64/1.14  #SimpNegUnit  : 0
% 1.64/1.14  #BackRed      : 0
% 1.64/1.14  
% 1.64/1.14  #Partial instantiations: 0
% 1.64/1.14  #Strategies tried      : 1
% 1.64/1.14  
% 1.64/1.14  Timing (in seconds)
% 1.64/1.14  ----------------------
% 1.64/1.14  Preprocessing        : 0.25
% 1.64/1.14  Parsing              : 0.14
% 1.64/1.14  CNF conversion       : 0.01
% 1.64/1.14  Main loop            : 0.11
% 1.64/1.14  Inferencing          : 0.04
% 1.64/1.14  Reduction            : 0.04
% 1.64/1.14  Demodulation         : 0.04
% 1.64/1.14  BG Simplification    : 0.01
% 1.64/1.14  Subsumption          : 0.02
% 1.64/1.14  Abstraction          : 0.01
% 1.64/1.14  MUC search           : 0.00
% 1.64/1.14  Cooper               : 0.00
% 1.64/1.14  Total                : 0.39
% 1.64/1.14  Index Insertion      : 0.00
% 1.64/1.14  Index Deletion       : 0.00
% 1.64/1.14  Index Matching       : 0.00
% 1.64/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
