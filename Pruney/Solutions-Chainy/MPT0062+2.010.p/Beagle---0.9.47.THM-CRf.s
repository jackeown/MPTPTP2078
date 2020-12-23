%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:08 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
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
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_59])).

tff(c_6,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_20,C_21,B_22] : k2_xboole_0(k4_xboole_0(A_20,C_21),k4_xboole_0(B_22,C_21)) = k4_xboole_0(k2_xboole_0(A_20,B_22),C_21) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_954,plain,(
    ! [A_43,B_44,B_45] : k2_xboole_0(k4_xboole_0(A_43,B_44),k4_xboole_0(B_45,k3_xboole_0(A_43,B_44))) = k4_xboole_0(k2_xboole_0(A_43,B_45),k3_xboole_0(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_139])).

tff(c_987,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_954])).

tff(c_10,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/2.20  
% 4.86/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/2.20  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 4.86/2.20  
% 4.86/2.20  %Foreground sorts:
% 4.86/2.20  
% 4.86/2.20  
% 4.86/2.20  %Background operators:
% 4.86/2.20  
% 4.86/2.20  
% 4.86/2.20  %Foreground operators:
% 4.86/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.86/2.20  tff('#skF_2', type, '#skF_2': $i).
% 4.86/2.20  tff('#skF_1', type, '#skF_1': $i).
% 4.86/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.86/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.86/2.20  
% 4.86/2.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.86/2.21  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.86/2.21  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.86/2.21  tff(f_36, negated_conjecture, ~(![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 4.86/2.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.86/2.21  tff(c_59, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/2.21  tff(c_74, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_59])).
% 4.86/2.21  tff(c_6, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/2.21  tff(c_139, plain, (![A_20, C_21, B_22]: (k2_xboole_0(k4_xboole_0(A_20, C_21), k4_xboole_0(B_22, C_21))=k4_xboole_0(k2_xboole_0(A_20, B_22), C_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.86/2.21  tff(c_954, plain, (![A_43, B_44, B_45]: (k2_xboole_0(k4_xboole_0(A_43, B_44), k4_xboole_0(B_45, k3_xboole_0(A_43, B_44)))=k4_xboole_0(k2_xboole_0(A_43, B_45), k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_139])).
% 4.86/2.21  tff(c_987, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_954])).
% 4.86/2.21  tff(c_10, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.86/2.21  tff(c_3213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_987, c_10])).
% 4.86/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/2.21  
% 4.86/2.21  Inference rules
% 4.86/2.21  ----------------------
% 4.86/2.21  #Ref     : 0
% 4.86/2.21  #Sup     : 844
% 4.86/2.21  #Fact    : 0
% 4.86/2.21  #Define  : 0
% 4.86/2.21  #Split   : 0
% 4.86/2.21  #Chain   : 0
% 4.86/2.21  #Close   : 0
% 4.86/2.21  
% 4.86/2.21  Ordering : KBO
% 4.86/2.21  
% 4.86/2.21  Simplification rules
% 4.86/2.21  ----------------------
% 4.86/2.21  #Subsume      : 79
% 4.86/2.21  #Demod        : 1070
% 4.86/2.21  #Tautology    : 374
% 4.86/2.21  #SimpNegUnit  : 0
% 4.86/2.21  #BackRed      : 1
% 4.86/2.21  
% 4.86/2.21  #Partial instantiations: 0
% 4.86/2.21  #Strategies tried      : 1
% 4.86/2.21  
% 4.86/2.21  Timing (in seconds)
% 4.86/2.21  ----------------------
% 4.86/2.21  Preprocessing        : 0.41
% 4.86/2.21  Parsing              : 0.21
% 4.86/2.21  CNF conversion       : 0.02
% 4.86/2.21  Main loop            : 0.97
% 4.86/2.21  Inferencing          : 0.30
% 4.86/2.21  Reduction            : 0.48
% 4.86/2.21  Demodulation         : 0.43
% 4.86/2.21  BG Simplification    : 0.04
% 4.86/2.21  Subsumption          : 0.11
% 4.86/2.21  Abstraction          : 0.07
% 4.86/2.21  MUC search           : 0.00
% 4.86/2.21  Cooper               : 0.00
% 4.86/2.21  Total                : 1.41
% 4.86/2.21  Index Insertion      : 0.00
% 4.86/2.21  Index Deletion       : 0.00
% 4.86/2.21  Index Matching       : 0.00
% 4.86/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
