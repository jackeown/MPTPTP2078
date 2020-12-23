%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:38 EST 2020

% Result     : Theorem 15.53s
% Output     : CNFRefutation 15.57s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  34 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_260,plain,(
    ! [A_45,B_46] : k2_xboole_0(k3_xboole_0(A_45,B_46),k4_xboole_0(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_275,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_260])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [A_9,B_10] : k2_xboole_0(k3_xboole_0(A_9,B_10),A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_118])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_417,plain,(
    ! [A_52,B_53,C_54] : k2_xboole_0(k2_xboole_0(A_52,B_53),C_54) = k2_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5278,plain,(
    ! [B_146,A_147,C_148] : k2_xboole_0(k2_xboole_0(B_146,A_147),C_148) = k2_xboole_0(A_147,k2_xboole_0(B_146,C_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_417])).

tff(c_22966,plain,(
    ! [A_300,B_301,C_302] : k2_xboole_0(A_300,k2_xboole_0(k3_xboole_0(A_300,B_301),C_302)) = k2_xboole_0(A_300,C_302) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_5278])).

tff(c_23287,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_22966])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12706,plain,(
    ! [A_215,B_216,C_217] : k2_xboole_0(k3_xboole_0(A_215,B_216),k2_xboole_0(k4_xboole_0(A_215,B_216),C_217)) = k2_xboole_0(A_215,C_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_417])).

tff(c_12939,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_12706])).

tff(c_50216,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23287,c_12939])).

tff(c_24,plain,(
    k2_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_50219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50216,c_25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.53/8.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/8.60  
% 15.57/8.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/8.60  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 15.57/8.60  
% 15.57/8.60  %Foreground sorts:
% 15.57/8.60  
% 15.57/8.60  
% 15.57/8.60  %Background operators:
% 15.57/8.60  
% 15.57/8.60  
% 15.57/8.60  %Foreground operators:
% 15.57/8.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.57/8.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.57/8.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.57/8.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.57/8.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.57/8.60  tff('#skF_2', type, '#skF_2': $i).
% 15.57/8.60  tff('#skF_1', type, '#skF_1': $i).
% 15.57/8.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.57/8.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.57/8.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.57/8.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.57/8.60  
% 15.57/8.61  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.57/8.61  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 15.57/8.61  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.57/8.61  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.57/8.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.57/8.61  tff(f_45, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 15.57/8.61  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 15.57/8.61  tff(f_52, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 15.57/8.61  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.57/8.61  tff(c_260, plain, (![A_45, B_46]: (k2_xboole_0(k3_xboole_0(A_45, B_46), k4_xboole_0(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.57/8.61  tff(c_275, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_260])).
% 15.57/8.61  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.57/8.61  tff(c_118, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.57/8.61  tff(c_126, plain, (![A_9, B_10]: (k2_xboole_0(k3_xboole_0(A_9, B_10), A_9)=A_9)), inference(resolution, [status(thm)], [c_10, c_118])).
% 15.57/8.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.57/8.61  tff(c_417, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k2_xboole_0(A_52, B_53), C_54)=k2_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.57/8.61  tff(c_5278, plain, (![B_146, A_147, C_148]: (k2_xboole_0(k2_xboole_0(B_146, A_147), C_148)=k2_xboole_0(A_147, k2_xboole_0(B_146, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_417])).
% 15.57/8.61  tff(c_22966, plain, (![A_300, B_301, C_302]: (k2_xboole_0(A_300, k2_xboole_0(k3_xboole_0(A_300, B_301), C_302))=k2_xboole_0(A_300, C_302))), inference(superposition, [status(thm), theory('equality')], [c_126, c_5278])).
% 15.57/8.61  tff(c_23287, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_275, c_22966])).
% 15.57/8.61  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.57/8.61  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.57/8.61  tff(c_12706, plain, (![A_215, B_216, C_217]: (k2_xboole_0(k3_xboole_0(A_215, B_216), k2_xboole_0(k4_xboole_0(A_215, B_216), C_217))=k2_xboole_0(A_215, C_217))), inference(superposition, [status(thm), theory('equality')], [c_20, c_417])).
% 15.57/8.61  tff(c_12939, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k2_xboole_0(A_5, k4_xboole_0(B_6, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_12706])).
% 15.57/8.61  tff(c_50216, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_23287, c_12939])).
% 15.57/8.61  tff(c_24, plain, (k2_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.57/8.61  tff(c_25, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 15.57/8.61  tff(c_50219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50216, c_25])).
% 15.57/8.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.57/8.61  
% 15.57/8.61  Inference rules
% 15.57/8.61  ----------------------
% 15.57/8.61  #Ref     : 0
% 15.57/8.61  #Sup     : 12449
% 15.57/8.61  #Fact    : 0
% 15.57/8.61  #Define  : 0
% 15.57/8.61  #Split   : 0
% 15.57/8.61  #Chain   : 0
% 15.57/8.61  #Close   : 0
% 15.57/8.61  
% 15.57/8.61  Ordering : KBO
% 15.57/8.61  
% 15.57/8.61  Simplification rules
% 15.57/8.61  ----------------------
% 15.57/8.61  #Subsume      : 580
% 15.57/8.61  #Demod        : 15474
% 15.57/8.61  #Tautology    : 7183
% 15.57/8.61  #SimpNegUnit  : 0
% 15.57/8.61  #BackRed      : 5
% 15.57/8.61  
% 15.57/8.61  #Partial instantiations: 0
% 15.57/8.61  #Strategies tried      : 1
% 15.57/8.61  
% 15.57/8.61  Timing (in seconds)
% 15.57/8.61  ----------------------
% 15.57/8.62  Preprocessing        : 0.26
% 15.57/8.62  Parsing              : 0.14
% 15.57/8.62  CNF conversion       : 0.02
% 15.57/8.62  Main loop            : 7.56
% 15.57/8.62  Inferencing          : 1.06
% 15.57/8.62  Reduction            : 5.12
% 15.57/8.62  Demodulation         : 4.82
% 15.57/8.62  BG Simplification    : 0.15
% 15.57/8.62  Subsumption          : 0.99
% 15.57/8.62  Abstraction          : 0.28
% 15.57/8.62  MUC search           : 0.00
% 15.57/8.62  Cooper               : 0.00
% 15.57/8.62  Total                : 7.84
% 15.57/8.62  Index Insertion      : 0.00
% 15.57/8.62  Index Deletion       : 0.00
% 15.57/8.62  Index Matching       : 0.00
% 15.57/8.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
