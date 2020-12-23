%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:36 EST 2020

% Result     : Theorem 13.23s
% Output     : CNFRefutation 13.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  42 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  34 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_477,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k3_xboole_0(A_35,B_36),k3_xboole_0(A_35,C_37)) = k3_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4667,plain,(
    ! [A_112,B_113,C_114] : k2_xboole_0(k3_xboole_0(A_112,B_113),k3_xboole_0(B_113,C_114)) = k3_xboole_0(B_113,k2_xboole_0(A_112,C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_477])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_232,plain,(
    ! [A_5,B_6,C_27] : k2_xboole_0(A_5,k2_xboole_0(k3_xboole_0(A_5,B_6),C_27)) = k2_xboole_0(A_5,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_11803,plain,(
    ! [A_172,B_173,C_174] : k2_xboole_0(A_172,k3_xboole_0(B_173,k2_xboole_0(A_172,C_174))) = k2_xboole_0(A_172,k3_xboole_0(B_173,C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4667,c_232])).

tff(c_12145,plain,(
    ! [A_172,C_174,B_2] : k2_xboole_0(A_172,k3_xboole_0(k2_xboole_0(A_172,C_174),B_2)) = k2_xboole_0(A_172,k3_xboole_0(B_2,C_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11803])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4836,plain,(
    ! [A_3,B_4,C_114] : k3_xboole_0(k2_xboole_0(A_3,B_4),k2_xboole_0(A_3,C_114)) = k2_xboole_0(A_3,k3_xboole_0(k2_xboole_0(A_3,B_4),C_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4667])).

tff(c_35545,plain,(
    ! [A_3,B_4,C_114] : k3_xboole_0(k2_xboole_0(A_3,B_4),k2_xboole_0(A_3,C_114)) = k2_xboole_0(A_3,k3_xboole_0(C_114,B_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12145,c_4836])).

tff(c_12,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_12])).

tff(c_35547,plain,(
    k2_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) != k2_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35545,c_13])).

tff(c_35551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.23/6.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.23/6.34  
% 13.23/6.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.23/6.34  %$ k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 13.23/6.34  
% 13.23/6.34  %Foreground sorts:
% 13.23/6.34  
% 13.23/6.34  
% 13.23/6.34  %Background operators:
% 13.23/6.34  
% 13.23/6.34  
% 13.23/6.34  %Foreground operators:
% 13.23/6.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.23/6.34  tff('#skF_2', type, '#skF_2': $i).
% 13.23/6.34  tff('#skF_3', type, '#skF_3': $i).
% 13.23/6.34  tff('#skF_1', type, '#skF_1': $i).
% 13.23/6.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.23/6.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.23/6.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.23/6.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.23/6.34  
% 13.23/6.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.23/6.35  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 13.23/6.35  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 13.23/6.35  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 13.23/6.35  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 13.23/6.35  tff(f_38, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_xboole_1)).
% 13.23/6.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.23/6.35  tff(c_477, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k3_xboole_0(A_35, B_36), k3_xboole_0(A_35, C_37))=k3_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.23/6.35  tff(c_4667, plain, (![A_112, B_113, C_114]: (k2_xboole_0(k3_xboole_0(A_112, B_113), k3_xboole_0(B_113, C_114))=k3_xboole_0(B_113, k2_xboole_0(A_112, C_114)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_477])).
% 13.23/6.35  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.23/6.35  tff(c_175, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.23/6.35  tff(c_232, plain, (![A_5, B_6, C_27]: (k2_xboole_0(A_5, k2_xboole_0(k3_xboole_0(A_5, B_6), C_27))=k2_xboole_0(A_5, C_27))), inference(superposition, [status(thm), theory('equality')], [c_6, c_175])).
% 13.23/6.35  tff(c_11803, plain, (![A_172, B_173, C_174]: (k2_xboole_0(A_172, k3_xboole_0(B_173, k2_xboole_0(A_172, C_174)))=k2_xboole_0(A_172, k3_xboole_0(B_173, C_174)))), inference(superposition, [status(thm), theory('equality')], [c_4667, c_232])).
% 13.23/6.35  tff(c_12145, plain, (![A_172, C_174, B_2]: (k2_xboole_0(A_172, k3_xboole_0(k2_xboole_0(A_172, C_174), B_2))=k2_xboole_0(A_172, k3_xboole_0(B_2, C_174)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11803])).
% 13.23/6.35  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.23/6.35  tff(c_4836, plain, (![A_3, B_4, C_114]: (k3_xboole_0(k2_xboole_0(A_3, B_4), k2_xboole_0(A_3, C_114))=k2_xboole_0(A_3, k3_xboole_0(k2_xboole_0(A_3, B_4), C_114)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4667])).
% 13.23/6.35  tff(c_35545, plain, (![A_3, B_4, C_114]: (k3_xboole_0(k2_xboole_0(A_3, B_4), k2_xboole_0(A_3, C_114))=k2_xboole_0(A_3, k3_xboole_0(C_114, B_4)))), inference(demodulation, [status(thm), theory('equality')], [c_12145, c_4836])).
% 13.23/6.35  tff(c_12, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.23/6.35  tff(c_13, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_12])).
% 13.23/6.35  tff(c_35547, plain, (k2_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35545, c_13])).
% 13.23/6.35  tff(c_35551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_35547])).
% 13.23/6.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.23/6.35  
% 13.23/6.35  Inference rules
% 13.23/6.35  ----------------------
% 13.23/6.35  #Ref     : 0
% 13.23/6.35  #Sup     : 8612
% 13.23/6.35  #Fact    : 0
% 13.23/6.35  #Define  : 0
% 13.23/6.35  #Split   : 0
% 13.23/6.35  #Chain   : 0
% 13.23/6.35  #Close   : 0
% 13.23/6.35  
% 13.23/6.35  Ordering : KBO
% 13.23/6.35  
% 13.23/6.35  Simplification rules
% 13.23/6.35  ----------------------
% 13.23/6.35  #Subsume      : 250
% 13.23/6.35  #Demod        : 12355
% 13.23/6.35  #Tautology    : 5394
% 13.23/6.35  #SimpNegUnit  : 0
% 13.23/6.35  #BackRed      : 4
% 13.23/6.35  
% 13.23/6.35  #Partial instantiations: 0
% 13.23/6.35  #Strategies tried      : 1
% 13.23/6.35  
% 13.23/6.35  Timing (in seconds)
% 13.23/6.35  ----------------------
% 13.23/6.36  Preprocessing        : 0.25
% 13.23/6.36  Parsing              : 0.14
% 13.23/6.36  CNF conversion       : 0.01
% 13.23/6.36  Main loop            : 5.36
% 13.23/6.36  Inferencing          : 1.14
% 13.23/6.36  Reduction            : 3.36
% 13.23/6.36  Demodulation         : 3.13
% 13.23/6.36  BG Simplification    : 0.13
% 13.23/6.36  Subsumption          : 0.58
% 13.23/6.36  Abstraction          : 0.32
% 13.23/6.36  MUC search           : 0.00
% 13.23/6.36  Cooper               : 0.00
% 13.23/6.36  Total                : 5.63
% 13.23/6.36  Index Insertion      : 0.00
% 13.23/6.36  Index Deletion       : 0.00
% 13.23/6.36  Index Matching       : 0.00
% 13.23/6.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
