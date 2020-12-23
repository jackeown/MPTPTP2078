%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:51 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [B_12,A_13] : k2_xboole_0(B_12,A_13) = k2_xboole_0(A_13,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_13] : k2_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_4])).

tff(c_113,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k4_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_113])).

tff(c_164,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_122])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [A_20,C_8] : k4_xboole_0(A_20,k2_xboole_0(A_20,C_8)) = k4_xboole_0(k1_xboole_0,C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_8])).

tff(c_187,plain,(
    ! [A_20,C_8] : k4_xboole_0(A_20,k2_xboole_0(A_20,C_8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_169])).

tff(c_12,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  
% 1.84/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.18  %$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.84/1.18  
% 1.84/1.18  %Foreground sorts:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Background operators:
% 1.84/1.18  
% 1.84/1.18  
% 1.84/1.18  %Foreground operators:
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.84/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.84/1.18  
% 1.84/1.19  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.84/1.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.84/1.19  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.84/1.19  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.84/1.19  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.84/1.19  tff(f_38, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.84/1.19  tff(c_10, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.84/1.19  tff(c_29, plain, (![B_12, A_13]: (k2_xboole_0(B_12, A_13)=k2_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.84/1.19  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.19  tff(c_45, plain, (![A_13]: (k2_xboole_0(k1_xboole_0, A_13)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_29, c_4])).
% 1.84/1.19  tff(c_113, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.19  tff(c_122, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k4_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_45, c_113])).
% 1.84/1.19  tff(c_164, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_122])).
% 1.84/1.19  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.19  tff(c_169, plain, (![A_20, C_8]: (k4_xboole_0(A_20, k2_xboole_0(A_20, C_8))=k4_xboole_0(k1_xboole_0, C_8))), inference(superposition, [status(thm), theory('equality')], [c_164, c_8])).
% 1.84/1.19  tff(c_187, plain, (![A_20, C_8]: (k4_xboole_0(A_20, k2_xboole_0(A_20, C_8))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_169])).
% 1.84/1.19  tff(c_12, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.84/1.19  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_187, c_12])).
% 1.84/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.19  
% 1.84/1.19  Inference rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Ref     : 0
% 1.84/1.19  #Sup     : 43
% 1.84/1.19  #Fact    : 0
% 1.84/1.19  #Define  : 0
% 1.84/1.19  #Split   : 0
% 1.84/1.19  #Chain   : 0
% 1.84/1.19  #Close   : 0
% 1.84/1.19  
% 1.84/1.19  Ordering : KBO
% 1.84/1.19  
% 1.84/1.19  Simplification rules
% 1.84/1.19  ----------------------
% 1.84/1.19  #Subsume      : 0
% 1.84/1.19  #Demod        : 17
% 1.84/1.19  #Tautology    : 33
% 1.84/1.19  #SimpNegUnit  : 0
% 1.84/1.19  #BackRed      : 1
% 1.84/1.19  
% 1.84/1.19  #Partial instantiations: 0
% 1.84/1.19  #Strategies tried      : 1
% 1.84/1.19  
% 1.84/1.19  Timing (in seconds)
% 1.84/1.19  ----------------------
% 1.84/1.19  Preprocessing        : 0.27
% 1.84/1.19  Parsing              : 0.16
% 1.84/1.19  CNF conversion       : 0.01
% 1.84/1.19  Main loop            : 0.15
% 1.84/1.19  Inferencing          : 0.05
% 1.84/1.19  Reduction            : 0.07
% 1.84/1.19  Demodulation         : 0.06
% 1.84/1.19  BG Simplification    : 0.01
% 1.84/1.19  Subsumption          : 0.02
% 1.84/1.19  Abstraction          : 0.01
% 1.84/1.19  MUC search           : 0.00
% 1.84/1.19  Cooper               : 0.00
% 1.84/1.19  Total                : 0.45
% 1.84/1.19  Index Insertion      : 0.00
% 1.84/1.19  Index Deletion       : 0.00
% 1.84/1.19  Index Matching       : 0.00
% 1.84/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
