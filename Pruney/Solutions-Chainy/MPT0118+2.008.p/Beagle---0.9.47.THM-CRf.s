%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:33 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   18 (  22 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  14 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_41,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k4_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [B_14,B_15,A_16] : k4_xboole_0(k3_xboole_0(B_14,B_15),k3_xboole_0(A_16,B_14)) = k3_xboole_0(B_14,k4_xboole_0(B_15,A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_41])).

tff(c_126,plain,(
    ! [A_1,B_2,A_16] : k4_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_16,B_2)) = k3_xboole_0(B_2,k4_xboole_0(A_1,A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_6,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  %$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.35  
% 2.48/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.48/1.36  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 2.48/1.36  tff(f_32, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 2.48/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.36  tff(c_41, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.36  tff(c_95, plain, (![B_14, B_15, A_16]: (k4_xboole_0(k3_xboole_0(B_14, B_15), k3_xboole_0(A_16, B_14))=k3_xboole_0(B_14, k4_xboole_0(B_15, A_16)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_41])).
% 2.48/1.36  tff(c_126, plain, (![A_1, B_2, A_16]: (k4_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_16, B_2))=k3_xboole_0(B_2, k4_xboole_0(A_1, A_16)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 2.48/1.36  tff(c_6, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.36  tff(c_7, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 2.48/1.36  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_7])).
% 2.48/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  Inference rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Ref     : 0
% 2.48/1.36  #Sup     : 158
% 2.48/1.36  #Fact    : 0
% 2.48/1.36  #Define  : 0
% 2.48/1.36  #Split   : 0
% 2.48/1.36  #Chain   : 0
% 2.48/1.36  #Close   : 0
% 2.48/1.36  
% 2.48/1.36  Ordering : KBO
% 2.48/1.36  
% 2.48/1.36  Simplification rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Subsume      : 31
% 2.48/1.36  #Demod        : 8
% 2.48/1.36  #Tautology    : 44
% 2.48/1.36  #SimpNegUnit  : 0
% 2.48/1.36  #BackRed      : 1
% 2.48/1.36  
% 2.48/1.36  #Partial instantiations: 0
% 2.48/1.36  #Strategies tried      : 1
% 2.48/1.36  
% 2.48/1.36  Timing (in seconds)
% 2.48/1.36  ----------------------
% 2.48/1.36  Preprocessing        : 0.25
% 2.48/1.36  Parsing              : 0.14
% 2.48/1.36  CNF conversion       : 0.01
% 2.48/1.36  Main loop            : 0.32
% 2.48/1.36  Inferencing          : 0.11
% 2.48/1.36  Reduction            : 0.13
% 2.48/1.36  Demodulation         : 0.11
% 2.48/1.36  BG Simplification    : 0.02
% 2.48/1.36  Subsumption          : 0.05
% 2.48/1.36  Abstraction          : 0.02
% 2.48/1.36  MUC search           : 0.00
% 2.48/1.36  Cooper               : 0.00
% 2.48/1.36  Total                : 0.59
% 2.48/1.36  Index Insertion      : 0.00
% 2.48/1.36  Index Deletion       : 0.00
% 2.48/1.36  Index Matching       : 0.00
% 2.48/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
