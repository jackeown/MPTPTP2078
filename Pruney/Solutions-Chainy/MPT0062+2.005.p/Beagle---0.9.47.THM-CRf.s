%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:08 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  17 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_10,B_11] : k4_xboole_0(k2_xboole_0(A_10,B_11),B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k4_xboole_0(A_14,B_15),k4_xboole_0(A_14,C_16)) = k4_xboole_0(A_14,k3_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_578,plain,(
    ! [A_34,B_35,B_36] : k2_xboole_0(k4_xboole_0(k2_xboole_0(A_34,B_35),B_36),k4_xboole_0(A_34,B_35)) = k4_xboole_0(k2_xboole_0(A_34,B_35),k3_xboole_0(B_36,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_646,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),k3_xboole_0(B_2,A_1)) = k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_578])).

tff(c_8,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_858,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_1'),k4_xboole_0('#skF_1','#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_8])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:00:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.37  
% 2.50/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.37  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.50/1.37  
% 2.50/1.37  %Foreground sorts:
% 2.50/1.37  
% 2.50/1.37  
% 2.50/1.37  %Background operators:
% 2.50/1.37  
% 2.50/1.37  
% 2.50/1.37  %Foreground operators:
% 2.50/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.37  
% 2.50/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.50/1.38  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.50/1.38  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 2.50/1.38  tff(f_34, negated_conjecture, ~(![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 2.50/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.38  tff(c_42, plain, (![A_10, B_11]: (k4_xboole_0(k2_xboole_0(A_10, B_11), B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.38  tff(c_51, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_42])).
% 2.50/1.38  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.38  tff(c_85, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k4_xboole_0(A_14, B_15), k4_xboole_0(A_14, C_16))=k4_xboole_0(A_14, k3_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.38  tff(c_578, plain, (![A_34, B_35, B_36]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(A_34, B_35), B_36), k4_xboole_0(A_34, B_35))=k4_xboole_0(k2_xboole_0(A_34, B_35), k3_xboole_0(B_36, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 2.50/1.38  tff(c_646, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), k3_xboole_0(B_2, A_1))=k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_578])).
% 2.50/1.38  tff(c_8, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.50/1.38  tff(c_858, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_1'), k4_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_8])).
% 2.50/1.38  tff(c_861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_858])).
% 2.50/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  Inference rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Ref     : 0
% 2.50/1.38  #Sup     : 228
% 2.50/1.38  #Fact    : 0
% 2.50/1.38  #Define  : 0
% 2.50/1.38  #Split   : 0
% 2.50/1.38  #Chain   : 0
% 2.50/1.38  #Close   : 0
% 2.50/1.38  
% 2.50/1.38  Ordering : KBO
% 2.50/1.38  
% 2.50/1.38  Simplification rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Subsume      : 15
% 2.50/1.38  #Demod        : 82
% 2.50/1.38  #Tautology    : 83
% 2.50/1.38  #SimpNegUnit  : 0
% 2.50/1.38  #BackRed      : 1
% 2.50/1.38  
% 2.50/1.38  #Partial instantiations: 0
% 2.50/1.38  #Strategies tried      : 1
% 2.50/1.38  
% 2.50/1.38  Timing (in seconds)
% 2.50/1.38  ----------------------
% 2.79/1.39  Preprocessing        : 0.25
% 2.79/1.39  Parsing              : 0.13
% 2.79/1.39  CNF conversion       : 0.01
% 2.79/1.39  Main loop            : 0.37
% 2.79/1.39  Inferencing          : 0.13
% 2.79/1.39  Reduction            : 0.16
% 2.79/1.39  Demodulation         : 0.14
% 2.79/1.39  BG Simplification    : 0.02
% 2.79/1.39  Subsumption          : 0.05
% 2.79/1.39  Abstraction          : 0.02
% 2.79/1.39  MUC search           : 0.00
% 2.79/1.39  Cooper               : 0.00
% 2.79/1.39  Total                : 0.64
% 2.79/1.39  Index Insertion      : 0.00
% 2.79/1.39  Index Deletion       : 0.00
% 2.79/1.39  Index Matching       : 0.00
% 2.79/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
