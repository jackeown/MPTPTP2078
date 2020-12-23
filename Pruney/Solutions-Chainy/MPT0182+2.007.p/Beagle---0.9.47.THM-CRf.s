%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:43 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  23 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_50,B_51,C_52] : k2_enumset1(A_50,A_50,B_51,C_52) = k1_enumset1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_48,B_49] : k1_enumset1(A_48,A_48,B_49) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_122,plain,(
    ! [A_91,B_92,C_93,D_94] : k2_xboole_0(k1_enumset1(A_91,B_92,C_93),k1_tarski(D_94)) = k2_enumset1(A_91,B_92,C_93,D_94) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_48,B_49,D_94] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(D_94)) = k2_enumset1(A_48,A_48,B_49,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_144,plain,(
    ! [A_100,B_101,D_102] : k2_xboole_0(k2_tarski(A_100,B_101),k1_tarski(D_102)) = k1_enumset1(A_100,B_101,D_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_131])).

tff(c_172,plain,(
    ! [B_105,A_106,D_107] : k2_xboole_0(k2_tarski(B_105,A_106),k1_tarski(D_107)) = k1_enumset1(A_106,B_105,D_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_144])).

tff(c_134,plain,(
    ! [A_48,B_49,D_94] : k2_xboole_0(k2_tarski(A_48,B_49),k1_tarski(D_94)) = k1_enumset1(A_48,B_49,D_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_131])).

tff(c_178,plain,(
    ! [B_105,A_106,D_107] : k1_enumset1(B_105,A_106,D_107) = k1_enumset1(A_106,B_105,D_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_134])).

tff(c_34,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:50:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.19  
% 2.06/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.19  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.06/1.19  
% 2.06/1.19  %Foreground sorts:
% 2.06/1.19  
% 2.06/1.19  
% 2.06/1.19  %Background operators:
% 2.06/1.19  
% 2.06/1.19  
% 2.06/1.19  %Foreground operators:
% 2.06/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.19  
% 2.06/1.20  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.06/1.20  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.06/1.20  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.20  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.06/1.20  tff(f_60, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.06/1.20  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.20  tff(c_24, plain, (![A_50, B_51, C_52]: (k2_enumset1(A_50, A_50, B_51, C_52)=k1_enumset1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.20  tff(c_22, plain, (![A_48, B_49]: (k1_enumset1(A_48, A_48, B_49)=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.20  tff(c_122, plain, (![A_91, B_92, C_93, D_94]: (k2_xboole_0(k1_enumset1(A_91, B_92, C_93), k1_tarski(D_94))=k2_enumset1(A_91, B_92, C_93, D_94))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.20  tff(c_131, plain, (![A_48, B_49, D_94]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(D_94))=k2_enumset1(A_48, A_48, B_49, D_94))), inference(superposition, [status(thm), theory('equality')], [c_22, c_122])).
% 2.06/1.20  tff(c_144, plain, (![A_100, B_101, D_102]: (k2_xboole_0(k2_tarski(A_100, B_101), k1_tarski(D_102))=k1_enumset1(A_100, B_101, D_102))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_131])).
% 2.06/1.20  tff(c_172, plain, (![B_105, A_106, D_107]: (k2_xboole_0(k2_tarski(B_105, A_106), k1_tarski(D_107))=k1_enumset1(A_106, B_105, D_107))), inference(superposition, [status(thm), theory('equality')], [c_6, c_144])).
% 2.06/1.20  tff(c_134, plain, (![A_48, B_49, D_94]: (k2_xboole_0(k2_tarski(A_48, B_49), k1_tarski(D_94))=k1_enumset1(A_48, B_49, D_94))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_131])).
% 2.06/1.20  tff(c_178, plain, (![B_105, A_106, D_107]: (k1_enumset1(B_105, A_106, D_107)=k1_enumset1(A_106, B_105, D_107))), inference(superposition, [status(thm), theory('equality')], [c_172, c_134])).
% 2.06/1.20  tff(c_34, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.20  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_34])).
% 2.06/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.20  
% 2.06/1.20  Inference rules
% 2.06/1.20  ----------------------
% 2.06/1.20  #Ref     : 0
% 2.06/1.20  #Sup     : 39
% 2.06/1.20  #Fact    : 0
% 2.06/1.20  #Define  : 0
% 2.06/1.20  #Split   : 0
% 2.06/1.20  #Chain   : 0
% 2.06/1.20  #Close   : 0
% 2.06/1.20  
% 2.06/1.20  Ordering : KBO
% 2.06/1.20  
% 2.06/1.20  Simplification rules
% 2.06/1.20  ----------------------
% 2.06/1.20  #Subsume      : 0
% 2.06/1.20  #Demod        : 7
% 2.06/1.20  #Tautology    : 33
% 2.06/1.20  #SimpNegUnit  : 0
% 2.06/1.20  #BackRed      : 1
% 2.06/1.20  
% 2.06/1.20  #Partial instantiations: 0
% 2.06/1.20  #Strategies tried      : 1
% 2.06/1.20  
% 2.06/1.20  Timing (in seconds)
% 2.06/1.20  ----------------------
% 2.06/1.20  Preprocessing        : 0.31
% 2.06/1.20  Parsing              : 0.17
% 2.06/1.20  CNF conversion       : 0.02
% 2.06/1.20  Main loop            : 0.13
% 2.06/1.20  Inferencing          : 0.05
% 2.06/1.20  Reduction            : 0.05
% 2.06/1.20  Demodulation         : 0.04
% 2.06/1.20  BG Simplification    : 0.02
% 2.06/1.20  Subsumption          : 0.02
% 2.06/1.20  Abstraction          : 0.01
% 2.06/1.20  MUC search           : 0.00
% 2.06/1.20  Cooper               : 0.00
% 2.06/1.20  Total                : 0.47
% 2.06/1.20  Index Insertion      : 0.00
% 2.06/1.20  Index Deletion       : 0.00
% 2.06/1.20  Index Matching       : 0.00
% 2.06/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
