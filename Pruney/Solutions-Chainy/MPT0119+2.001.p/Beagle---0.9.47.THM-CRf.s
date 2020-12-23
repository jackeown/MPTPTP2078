%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:33 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   19 (  26 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k3_xboole_0(A_18,B_19),k3_xboole_0(A_18,C_20)) = k3_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    ! [B_21,B_22,A_23] : k2_xboole_0(k3_xboole_0(B_21,B_22),k3_xboole_0(A_23,B_21)) = k3_xboole_0(B_21,k2_xboole_0(B_22,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_127,plain,(
    ! [A_1,B_2,A_23] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(A_23,B_2)) = k3_xboole_0(B_2,k2_xboole_0(A_1,A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k3_xboole_0(A_5,B_6),k3_xboole_0(C_7,B_6)) = k3_xboole_0(k4_xboole_0(A_5,C_7),B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(C_17,B_16)) = k3_xboole_0(k4_xboole_0(A_15,C_17),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_15,C_17,B_16] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_15,C_17),B_16),k4_xboole_0(k3_xboole_0(C_17,B_16),k3_xboole_0(A_15,B_16))) = k5_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(C_17,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_1912,plain,(
    ! [A_51,C_52,B_53] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_51,C_52),B_53),k3_xboole_0(k4_xboole_0(C_52,A_51),B_53)) = k5_xboole_0(k3_xboole_0(A_51,B_53),k3_xboole_0(C_52,B_53)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_1961,plain,(
    ! [A_51,B_2,C_52] : k5_xboole_0(k3_xboole_0(A_51,B_2),k3_xboole_0(C_52,B_2)) = k3_xboole_0(B_2,k2_xboole_0(k4_xboole_0(A_51,C_52),k4_xboole_0(C_52,A_51))) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1912])).

tff(c_2085,plain,(
    ! [A_51,B_2,C_52] : k5_xboole_0(k3_xboole_0(A_51,B_2),k3_xboole_0(C_52,B_2)) = k3_xboole_0(B_2,k5_xboole_0(A_51,C_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1961])).

tff(c_10,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k5_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.69  
% 3.77/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.69  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.77/1.69  
% 3.77/1.69  %Foreground sorts:
% 3.77/1.69  
% 3.77/1.69  
% 3.77/1.69  %Background operators:
% 3.77/1.69  
% 3.77/1.69  
% 3.77/1.69  %Foreground operators:
% 3.77/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.77/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.77/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.77/1.69  
% 3.77/1.71  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.77/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.77/1.71  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 3.77/1.71  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 3.77/1.71  tff(f_36, negated_conjecture, ~(![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 3.77/1.71  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.77/1.71  tff(c_83, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k3_xboole_0(A_18, C_20))=k3_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.77/1.71  tff(c_104, plain, (![B_21, B_22, A_23]: (k2_xboole_0(k3_xboole_0(B_21, B_22), k3_xboole_0(A_23, B_21))=k3_xboole_0(B_21, k2_xboole_0(B_22, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 3.77/1.71  tff(c_127, plain, (![A_1, B_2, A_23]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k3_xboole_0(A_23, B_2))=k3_xboole_0(B_2, k2_xboole_0(A_1, A_23)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 3.77/1.71  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k3_xboole_0(A_5, B_6), k3_xboole_0(C_7, B_6))=k3_xboole_0(k4_xboole_0(A_5, C_7), B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.71  tff(c_54, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), k3_xboole_0(C_17, B_16))=k3_xboole_0(k4_xboole_0(A_15, C_17), B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.71  tff(c_60, plain, (![A_15, C_17, B_16]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_15, C_17), B_16), k4_xboole_0(k3_xboole_0(C_17, B_16), k3_xboole_0(A_15, B_16)))=k5_xboole_0(k3_xboole_0(A_15, B_16), k3_xboole_0(C_17, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4])).
% 3.77/1.71  tff(c_1912, plain, (![A_51, C_52, B_53]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_51, C_52), B_53), k3_xboole_0(k4_xboole_0(C_52, A_51), B_53))=k5_xboole_0(k3_xboole_0(A_51, B_53), k3_xboole_0(C_52, B_53)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_60])).
% 3.77/1.71  tff(c_1961, plain, (![A_51, B_2, C_52]: (k5_xboole_0(k3_xboole_0(A_51, B_2), k3_xboole_0(C_52, B_2))=k3_xboole_0(B_2, k2_xboole_0(k4_xboole_0(A_51, C_52), k4_xboole_0(C_52, A_51))))), inference(superposition, [status(thm), theory('equality')], [c_127, c_1912])).
% 3.77/1.71  tff(c_2085, plain, (![A_51, B_2, C_52]: (k5_xboole_0(k3_xboole_0(A_51, B_2), k3_xboole_0(C_52, B_2))=k3_xboole_0(B_2, k5_xboole_0(A_51, C_52)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1961])).
% 3.77/1.71  tff(c_10, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.77/1.71  tff(c_11, plain, (k5_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 3.77/1.71  tff(c_2103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2085, c_11])).
% 3.77/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.71  
% 3.77/1.71  Inference rules
% 3.77/1.71  ----------------------
% 3.77/1.71  #Ref     : 0
% 3.77/1.71  #Sup     : 562
% 3.77/1.71  #Fact    : 0
% 3.77/1.71  #Define  : 0
% 3.77/1.71  #Split   : 0
% 3.77/1.71  #Chain   : 0
% 3.77/1.71  #Close   : 0
% 3.77/1.71  
% 3.77/1.71  Ordering : KBO
% 3.77/1.71  
% 3.77/1.71  Simplification rules
% 3.77/1.71  ----------------------
% 3.77/1.71  #Subsume      : 66
% 3.77/1.71  #Demod        : 137
% 3.77/1.71  #Tautology    : 110
% 3.77/1.71  #SimpNegUnit  : 0
% 3.77/1.71  #BackRed      : 2
% 3.77/1.71  
% 3.77/1.71  #Partial instantiations: 0
% 3.77/1.71  #Strategies tried      : 1
% 3.77/1.71  
% 3.77/1.71  Timing (in seconds)
% 3.77/1.71  ----------------------
% 3.77/1.71  Preprocessing        : 0.25
% 3.77/1.71  Parsing              : 0.14
% 3.77/1.71  CNF conversion       : 0.01
% 3.77/1.71  Main loop            : 0.62
% 3.77/1.71  Inferencing          : 0.19
% 3.77/1.71  Reduction            : 0.27
% 3.77/1.71  Demodulation         : 0.24
% 3.77/1.71  BG Simplification    : 0.04
% 3.77/1.71  Subsumption          : 0.08
% 3.77/1.71  Abstraction          : 0.04
% 3.77/1.71  MUC search           : 0.00
% 3.77/1.71  Cooper               : 0.00
% 3.77/1.71  Total                : 0.90
% 3.77/1.71  Index Insertion      : 0.00
% 3.77/1.71  Index Deletion       : 0.00
% 3.77/1.71  Index Matching       : 0.00
% 3.77/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
