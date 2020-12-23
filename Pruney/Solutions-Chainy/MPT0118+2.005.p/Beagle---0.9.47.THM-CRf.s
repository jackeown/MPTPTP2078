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
% DateTime   : Thu Dec  3 09:45:32 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   26 (  33 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_512,plain,(
    ! [A_47,B_48,C_49] : k4_xboole_0(k3_xboole_0(A_47,B_48),C_49) = k3_xboole_0(A_47,k4_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2517,plain,(
    ! [A_94,B_95,C_96] : k4_xboole_0(k3_xboole_0(A_94,B_95),C_96) = k3_xboole_0(B_95,k4_xboole_0(A_94,C_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_512])).

tff(c_2626,plain,(
    ! [B_12,A_11,C_13] : k3_xboole_0(B_12,k4_xboole_0(A_11,C_13)) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2517])).

tff(c_107,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_20,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_22,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_2'))) != k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_21])).

tff(c_401,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_22])).

tff(c_6165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2626,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.23  
% 5.87/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.24  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.87/2.24  
% 5.87/2.24  %Foreground sorts:
% 5.87/2.24  
% 5.87/2.24  
% 5.87/2.24  %Background operators:
% 5.87/2.24  
% 5.87/2.24  
% 5.87/2.24  %Foreground operators:
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.87/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.87/2.24  tff('#skF_2', type, '#skF_2': $i).
% 5.87/2.24  tff('#skF_3', type, '#skF_3': $i).
% 5.87/2.24  tff('#skF_1', type, '#skF_1': $i).
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.87/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.87/2.24  
% 5.87/2.24  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.87/2.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.87/2.24  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.87/2.24  tff(f_48, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 5.87/2.24  tff(c_12, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.87/2.24  tff(c_512, plain, (![A_47, B_48, C_49]: (k4_xboole_0(k3_xboole_0(A_47, B_48), C_49)=k3_xboole_0(A_47, k4_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.24  tff(c_2517, plain, (![A_94, B_95, C_96]: (k4_xboole_0(k3_xboole_0(A_94, B_95), C_96)=k3_xboole_0(B_95, k4_xboole_0(A_94, C_96)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_512])).
% 5.87/2.24  tff(c_2626, plain, (![B_12, A_11, C_13]: (k3_xboole_0(B_12, k4_xboole_0(A_11, C_13))=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2517])).
% 5.87/2.24  tff(c_107, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.87/2.24  tff(c_126, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 5.87/2.24  tff(c_20, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.87/2.24  tff(c_21, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 5.87/2.24  tff(c_22, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_2')))!=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_21])).
% 5.87/2.24  tff(c_401, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_22])).
% 5.87/2.24  tff(c_6165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2626, c_401])).
% 5.87/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.87/2.24  
% 5.87/2.24  Inference rules
% 5.87/2.24  ----------------------
% 5.87/2.24  #Ref     : 2
% 5.87/2.24  #Sup     : 1637
% 5.87/2.24  #Fact    : 0
% 5.87/2.24  #Define  : 0
% 5.87/2.24  #Split   : 7
% 5.87/2.24  #Chain   : 0
% 5.87/2.24  #Close   : 0
% 5.87/2.24  
% 5.87/2.24  Ordering : KBO
% 5.87/2.24  
% 5.87/2.24  Simplification rules
% 5.87/2.24  ----------------------
% 5.87/2.24  #Subsume      : 417
% 5.87/2.24  #Demod        : 746
% 5.87/2.24  #Tautology    : 413
% 5.87/2.24  #SimpNegUnit  : 10
% 5.87/2.24  #BackRed      : 3
% 5.87/2.24  
% 5.87/2.24  #Partial instantiations: 0
% 5.87/2.24  #Strategies tried      : 1
% 5.87/2.24  
% 5.87/2.24  Timing (in seconds)
% 5.87/2.24  ----------------------
% 5.87/2.25  Preprocessing        : 0.29
% 5.87/2.25  Parsing              : 0.15
% 5.87/2.25  CNF conversion       : 0.02
% 5.87/2.25  Main loop            : 1.21
% 5.87/2.25  Inferencing          : 0.31
% 5.87/2.25  Reduction            : 0.62
% 5.87/2.25  Demodulation         : 0.54
% 5.87/2.25  BG Simplification    : 0.05
% 5.87/2.25  Subsumption          : 0.16
% 5.87/2.25  Abstraction          : 0.07
% 5.87/2.25  MUC search           : 0.00
% 5.87/2.25  Cooper               : 0.00
% 5.87/2.25  Total                : 1.52
% 5.87/2.25  Index Insertion      : 0.00
% 5.87/2.25  Index Deletion       : 0.00
% 5.87/2.25  Index Matching       : 0.00
% 5.87/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
