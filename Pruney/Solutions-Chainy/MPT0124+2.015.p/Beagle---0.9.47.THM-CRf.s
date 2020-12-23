%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:37 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(C,B)
       => k4_xboole_0(A,C) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,k4_xboole_0(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_14)) = k4_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3'))) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_20,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_19])).

tff(c_21,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.66/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.11  
% 1.66/1.11  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(C, B) => (k4_xboole_0(A, C) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, k4_xboole_0(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 1.66/1.11  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.66/1.11  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.66/1.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.66/1.11  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.66/1.11  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.66/1.11  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.11  tff(c_64, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.11  tff(c_68, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_64])).
% 1.66/1.11  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.11  tff(c_72, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_68, c_6])).
% 1.66/1.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.11  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.11  tff(c_12, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_14))=k4_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.11  tff(c_16, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.11  tff(c_19, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3')))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 1.66/1.11  tff(c_20, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_19])).
% 1.66/1.11  tff(c_21, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 1.66/1.11  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_21])).
% 1.66/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  Inference rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Ref     : 0
% 1.66/1.11  #Sup     : 14
% 1.66/1.11  #Fact    : 0
% 1.66/1.11  #Define  : 0
% 1.66/1.11  #Split   : 0
% 1.66/1.11  #Chain   : 0
% 1.66/1.11  #Close   : 0
% 1.66/1.11  
% 1.66/1.11  Ordering : KBO
% 1.66/1.11  
% 1.66/1.11  Simplification rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Subsume      : 0
% 1.66/1.11  #Demod        : 4
% 1.66/1.11  #Tautology    : 12
% 1.66/1.11  #SimpNegUnit  : 0
% 1.66/1.11  #BackRed      : 1
% 1.66/1.11  
% 1.66/1.11  #Partial instantiations: 0
% 1.66/1.11  #Strategies tried      : 1
% 1.66/1.11  
% 1.66/1.11  Timing (in seconds)
% 1.66/1.11  ----------------------
% 1.66/1.12  Preprocessing        : 0.27
% 1.66/1.12  Parsing              : 0.14
% 1.66/1.12  CNF conversion       : 0.01
% 1.66/1.12  Main loop            : 0.08
% 1.66/1.12  Inferencing          : 0.03
% 1.66/1.12  Reduction            : 0.03
% 1.66/1.12  Demodulation         : 0.02
% 1.66/1.12  BG Simplification    : 0.01
% 1.66/1.12  Subsumption          : 0.01
% 1.66/1.12  Abstraction          : 0.01
% 1.66/1.12  MUC search           : 0.00
% 1.66/1.12  Cooper               : 0.00
% 1.66/1.12  Total                : 0.37
% 1.66/1.12  Index Insertion      : 0.00
% 1.66/1.12  Index Deletion       : 0.00
% 1.66/1.12  Index Matching       : 0.00
% 1.66/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
