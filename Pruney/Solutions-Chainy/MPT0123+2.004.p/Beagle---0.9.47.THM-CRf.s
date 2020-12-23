%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   19 (  22 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   11 (  14 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

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
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,k4_xboole_0(B_14,C_15))) = k3_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k4_xboole_0(k3_xboole_0(A_3,B_4),k3_xboole_0(A_3,C_5)) = k3_xboole_0(A_3,k4_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_13,B_14,C_15] : k3_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) = k3_xboole_0(A_13,k4_xboole_0(B_14,k4_xboole_0(B_14,C_15))) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_4])).

tff(c_80,plain,(
    ! [A_13,B_14,C_15] : k3_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)) = k3_xboole_0(A_13,k3_xboole_0(B_14,C_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_6,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.13  %$ k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.75/1.13  
% 1.75/1.13  %Foreground sorts:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Background operators:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Foreground operators:
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.75/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.75/1.13  
% 1.75/1.14  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.75/1.14  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 1.75/1.14  tff(f_32, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_xboole_1)).
% 1.75/1.14  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.14  tff(c_35, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.14  tff(c_47, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))=k3_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_35, c_2])).
% 1.75/1.14  tff(c_4, plain, (![A_3, B_4, C_5]: (k4_xboole_0(k3_xboole_0(A_3, B_4), k3_xboole_0(A_3, C_5))=k3_xboole_0(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.14  tff(c_56, plain, (![A_13, B_14, C_15]: (k3_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15))=k3_xboole_0(A_13, k4_xboole_0(B_14, k4_xboole_0(B_14, C_15))))), inference(superposition, [status(thm), theory('equality')], [c_47, c_4])).
% 1.75/1.14  tff(c_80, plain, (![A_13, B_14, C_15]: (k3_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15))=k3_xboole_0(A_13, k3_xboole_0(B_14, C_15)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 1.75/1.14  tff(c_6, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.14  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_6])).
% 1.75/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  Inference rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Ref     : 0
% 1.75/1.14  #Sup     : 32
% 1.75/1.14  #Fact    : 0
% 1.75/1.14  #Define  : 0
% 1.75/1.14  #Split   : 0
% 1.75/1.14  #Chain   : 0
% 1.75/1.14  #Close   : 0
% 1.75/1.14  
% 1.75/1.14  Ordering : KBO
% 1.75/1.14  
% 1.75/1.14  Simplification rules
% 1.75/1.14  ----------------------
% 1.75/1.14  #Subsume      : 0
% 1.75/1.14  #Demod        : 12
% 1.75/1.14  #Tautology    : 13
% 1.75/1.14  #SimpNegUnit  : 0
% 1.75/1.14  #BackRed      : 2
% 1.75/1.14  
% 1.75/1.14  #Partial instantiations: 0
% 1.75/1.14  #Strategies tried      : 1
% 1.75/1.14  
% 1.75/1.14  Timing (in seconds)
% 1.75/1.14  ----------------------
% 1.75/1.14  Preprocessing        : 0.24
% 1.75/1.14  Parsing              : 0.13
% 1.75/1.14  CNF conversion       : 0.01
% 1.75/1.14  Main loop            : 0.14
% 1.75/1.14  Inferencing          : 0.06
% 1.75/1.14  Reduction            : 0.04
% 1.75/1.14  Demodulation         : 0.04
% 1.75/1.15  BG Simplification    : 0.01
% 1.75/1.15  Subsumption          : 0.02
% 1.75/1.15  Abstraction          : 0.01
% 1.75/1.15  MUC search           : 0.00
% 1.75/1.15  Cooper               : 0.00
% 1.75/1.15  Total                : 0.39
% 1.75/1.15  Index Insertion      : 0.00
% 1.75/1.15  Index Deletion       : 0.00
% 1.75/1.15  Index Matching       : 0.00
% 1.75/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
