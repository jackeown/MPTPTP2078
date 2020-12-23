%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:32 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.72s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  32 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_223,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(k3_xboole_0(A_31,B_32),C_33) = k3_xboole_0(A_31,k4_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_525,plain,(
    ! [A_45,B_46,C_47] : k4_xboole_0(k3_xboole_0(A_45,B_46),C_47) = k3_xboole_0(B_46,k4_xboole_0(A_45,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_223])).

tff(c_560,plain,(
    ! [B_13,A_12,C_14] : k3_xboole_0(B_13,k4_xboole_0(A_12,C_14)) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_525])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [A_36,B_37,C_38] : k3_xboole_0(k3_xboole_0(A_36,B_37),C_38) = k3_xboole_0(A_36,k3_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_335,plain,(
    ! [A_39,C_40] : k3_xboole_0(A_39,k3_xboole_0(A_39,C_40)) = k3_xboole_0(A_39,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_263])).

tff(c_441,plain,(
    ! [A_43,B_44] : k3_xboole_0(A_43,k3_xboole_0(B_44,A_43)) = k3_xboole_0(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_335])).

tff(c_473,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,k3_xboole_0(B_44,A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_8])).

tff(c_515,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(B_44,A_43)) = k4_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_473])).

tff(c_16,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_18,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17])).

tff(c_582,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_18])).

tff(c_4150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_582])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:06:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/3.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/3.12  
% 7.65/3.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/3.12  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 7.65/3.12  
% 7.65/3.12  %Foreground sorts:
% 7.65/3.12  
% 7.65/3.12  
% 7.65/3.12  %Background operators:
% 7.65/3.12  
% 7.65/3.12  
% 7.65/3.12  %Foreground operators:
% 7.65/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/3.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.65/3.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.65/3.12  tff('#skF_2', type, '#skF_2': $i).
% 7.65/3.12  tff('#skF_3', type, '#skF_3': $i).
% 7.65/3.12  tff('#skF_1', type, '#skF_1': $i).
% 7.65/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/3.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.65/3.12  
% 7.72/3.13  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.72/3.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.72/3.13  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.72/3.13  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.72/3.13  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.72/3.13  tff(f_42, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 7.72/3.13  tff(c_12, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.72/3.13  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.72/3.13  tff(c_223, plain, (![A_31, B_32, C_33]: (k4_xboole_0(k3_xboole_0(A_31, B_32), C_33)=k3_xboole_0(A_31, k4_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.72/3.13  tff(c_525, plain, (![A_45, B_46, C_47]: (k4_xboole_0(k3_xboole_0(A_45, B_46), C_47)=k3_xboole_0(B_46, k4_xboole_0(A_45, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_223])).
% 7.72/3.13  tff(c_560, plain, (![B_13, A_12, C_14]: (k3_xboole_0(B_13, k4_xboole_0(A_12, C_14))=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_525])).
% 7.72/3.13  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.72/3.13  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.72/3.13  tff(c_263, plain, (![A_36, B_37, C_38]: (k3_xboole_0(k3_xboole_0(A_36, B_37), C_38)=k3_xboole_0(A_36, k3_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.72/3.13  tff(c_335, plain, (![A_39, C_40]: (k3_xboole_0(A_39, k3_xboole_0(A_39, C_40))=k3_xboole_0(A_39, C_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_263])).
% 7.72/3.13  tff(c_441, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k3_xboole_0(B_44, A_43))=k3_xboole_0(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_2, c_335])).
% 7.72/3.13  tff(c_473, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, k3_xboole_0(B_44, A_43)))), inference(superposition, [status(thm), theory('equality')], [c_441, c_8])).
% 7.72/3.13  tff(c_515, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(B_44, A_43))=k4_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_473])).
% 7.72/3.13  tff(c_16, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.72/3.13  tff(c_17, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 7.72/3.13  tff(c_18, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17])).
% 7.72/3.13  tff(c_582, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_18])).
% 7.72/3.13  tff(c_4150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_582])).
% 7.72/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.72/3.13  
% 7.72/3.13  Inference rules
% 7.72/3.13  ----------------------
% 7.72/3.13  #Ref     : 0
% 7.72/3.13  #Sup     : 1070
% 7.72/3.13  #Fact    : 0
% 7.72/3.13  #Define  : 0
% 7.72/3.13  #Split   : 0
% 7.72/3.13  #Chain   : 0
% 7.72/3.13  #Close   : 0
% 7.72/3.13  
% 7.72/3.13  Ordering : KBO
% 7.72/3.13  
% 7.72/3.13  Simplification rules
% 7.72/3.13  ----------------------
% 7.72/3.13  #Subsume      : 111
% 7.72/3.13  #Demod        : 765
% 7.72/3.13  #Tautology    : 281
% 7.72/3.13  #SimpNegUnit  : 0
% 7.72/3.14  #BackRed      : 2
% 7.72/3.14  
% 7.72/3.14  #Partial instantiations: 0
% 7.72/3.14  #Strategies tried      : 1
% 7.72/3.14  
% 7.72/3.14  Timing (in seconds)
% 7.72/3.14  ----------------------
% 7.72/3.14  Preprocessing        : 0.44
% 7.72/3.14  Parsing              : 0.24
% 7.72/3.14  CNF conversion       : 0.02
% 7.72/3.14  Main loop            : 1.76
% 7.72/3.14  Inferencing          : 0.41
% 7.72/3.14  Reduction            : 1.02
% 7.72/3.14  Demodulation         : 0.94
% 7.72/3.14  BG Simplification    : 0.07
% 7.72/3.14  Subsumption          : 0.19
% 7.81/3.14  Abstraction          : 0.10
% 7.81/3.14  MUC search           : 0.00
% 7.81/3.14  Cooper               : 0.00
% 7.81/3.14  Total                : 2.24
% 7.81/3.14  Index Insertion      : 0.00
% 7.81/3.14  Index Deletion       : 0.00
% 7.81/3.14  Index Matching       : 0.00
% 7.81/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
