%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:32 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k3_xboole_0(A_5,B_6)) = k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_460,plain,(
    ! [A_62,B_63] : k2_xboole_0(k4_xboole_0(A_62,B_63),k3_xboole_0(A_62,B_63)) = k2_xboole_0(A_62,k4_xboole_0(A_62,B_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_99])).

tff(c_487,plain,(
    ! [A_62,B_63] : k2_xboole_0(k3_xboole_0(A_62,B_63),k4_xboole_0(A_62,B_63)) = k2_xboole_0(A_62,k4_xboole_0(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_2])).

tff(c_522,plain,(
    ! [A_64,B_65] : k2_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_487])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_574,plain,(
    ! [A_66] : r1_tarski(A_66,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_12])).

tff(c_14,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_164,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r1_tarski(C_36,B_35)
      | ~ r1_tarski(C_36,A_34)
      | v1_xboole_0(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [C_36] :
      ( ~ r1_tarski(C_36,'#skF_1')
      | ~ r1_tarski(C_36,'#skF_2')
      | v1_xboole_0(C_36) ) ),
    inference(resolution,[status(thm)],[c_14,c_164])).

tff(c_578,plain,
    ( ~ r1_tarski('#skF_2','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_574,c_167])).

tff(c_581,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_578])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:41:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.30  
% 2.50/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.31  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.50/1.31  
% 2.50/1.31  %Foreground sorts:
% 2.50/1.31  
% 2.50/1.31  
% 2.50/1.31  %Background operators:
% 2.50/1.31  
% 2.50/1.31  
% 2.50/1.31  %Foreground operators:
% 2.50/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.31  
% 2.50/1.32  tff(f_54, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.50/1.32  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.50/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.50/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.50/1.32  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.50/1.32  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.50/1.32  tff(f_43, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.50/1.32  tff(c_18, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.32  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.32  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.32  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.32  tff(c_84, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.32  tff(c_99, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k3_xboole_0(A_5, B_6))=k2_xboole_0(k4_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 2.50/1.32  tff(c_460, plain, (![A_62, B_63]: (k2_xboole_0(k4_xboole_0(A_62, B_63), k3_xboole_0(A_62, B_63))=k2_xboole_0(A_62, k4_xboole_0(A_62, B_63)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_99])).
% 2.50/1.32  tff(c_487, plain, (![A_62, B_63]: (k2_xboole_0(k3_xboole_0(A_62, B_63), k4_xboole_0(A_62, B_63))=k2_xboole_0(A_62, k4_xboole_0(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_460, c_2])).
% 2.50/1.32  tff(c_522, plain, (![A_64, B_65]: (k2_xboole_0(A_64, k4_xboole_0(A_64, B_65))=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_487])).
% 2.50/1.32  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.32  tff(c_574, plain, (![A_66]: (r1_tarski(A_66, A_66))), inference(superposition, [status(thm), theory('equality')], [c_522, c_12])).
% 2.50/1.32  tff(c_14, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.50/1.32  tff(c_164, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r1_tarski(C_36, B_35) | ~r1_tarski(C_36, A_34) | v1_xboole_0(C_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.32  tff(c_167, plain, (![C_36]: (~r1_tarski(C_36, '#skF_1') | ~r1_tarski(C_36, '#skF_2') | v1_xboole_0(C_36))), inference(resolution, [status(thm)], [c_14, c_164])).
% 2.50/1.32  tff(c_578, plain, (~r1_tarski('#skF_2', '#skF_1') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_574, c_167])).
% 2.50/1.32  tff(c_581, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_578])).
% 2.50/1.32  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_581])).
% 2.50/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.32  
% 2.50/1.32  Inference rules
% 2.50/1.32  ----------------------
% 2.50/1.32  #Ref     : 0
% 2.50/1.32  #Sup     : 146
% 2.50/1.32  #Fact    : 0
% 2.50/1.32  #Define  : 0
% 2.50/1.32  #Split   : 0
% 2.50/1.32  #Chain   : 0
% 2.50/1.32  #Close   : 0
% 2.50/1.32  
% 2.50/1.32  Ordering : KBO
% 2.50/1.32  
% 2.50/1.32  Simplification rules
% 2.50/1.32  ----------------------
% 2.50/1.32  #Subsume      : 2
% 2.50/1.32  #Demod        : 56
% 2.50/1.32  #Tautology    : 55
% 2.50/1.32  #SimpNegUnit  : 1
% 2.50/1.32  #BackRed      : 2
% 2.50/1.32  
% 2.50/1.32  #Partial instantiations: 0
% 2.50/1.32  #Strategies tried      : 1
% 2.50/1.32  
% 2.50/1.32  Timing (in seconds)
% 2.50/1.32  ----------------------
% 2.50/1.32  Preprocessing        : 0.27
% 2.50/1.32  Parsing              : 0.15
% 2.50/1.32  CNF conversion       : 0.02
% 2.50/1.32  Main loop            : 0.30
% 2.50/1.32  Inferencing          : 0.10
% 2.50/1.32  Reduction            : 0.12
% 2.50/1.32  Demodulation         : 0.10
% 2.50/1.32  BG Simplification    : 0.01
% 2.50/1.32  Subsumption          : 0.05
% 2.50/1.32  Abstraction          : 0.01
% 2.50/1.32  MUC search           : 0.00
% 2.50/1.32  Cooper               : 0.00
% 2.50/1.32  Total                : 0.60
% 2.50/1.32  Index Insertion      : 0.00
% 2.50/1.32  Index Deletion       : 0.00
% 2.50/1.32  Index Matching       : 0.00
% 2.50/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
