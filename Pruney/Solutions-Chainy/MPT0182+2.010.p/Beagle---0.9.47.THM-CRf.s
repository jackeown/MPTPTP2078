%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:43 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_78,B_79,C_80,D_81] : k2_xboole_0(k1_enumset1(A_78,B_79,C_80),k1_tarski(D_81)) = k2_enumset1(A_78,B_79,C_80,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_127,plain,(
    ! [A_35,B_36,D_81] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_81)) = k2_enumset1(A_35,A_35,B_36,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_118])).

tff(c_140,plain,(
    ! [A_87,B_88,D_89] : k2_xboole_0(k2_tarski(A_87,B_88),k1_tarski(D_89)) = k1_enumset1(A_87,B_88,D_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_168,plain,(
    ! [B_92,A_93,D_94] : k2_xboole_0(k2_tarski(B_92,A_93),k1_tarski(D_94)) = k1_enumset1(A_93,B_92,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_140])).

tff(c_130,plain,(
    ! [A_35,B_36,D_81] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_81)) = k1_enumset1(A_35,B_36,D_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_174,plain,(
    ! [B_92,A_93,D_94] : k1_enumset1(B_92,A_93,D_94) = k1_enumset1(A_93,B_92,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_130])).

tff(c_30,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.19  
% 2.01/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.20  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.01/1.20  
% 2.01/1.20  %Foreground sorts:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Background operators:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Foreground operators:
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.01/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.20  
% 2.01/1.20  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.01/1.20  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.01/1.20  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.01/1.20  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.01/1.20  tff(f_56, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 2.01/1.20  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.20  tff(c_20, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.01/1.20  tff(c_18, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.20  tff(c_118, plain, (![A_78, B_79, C_80, D_81]: (k2_xboole_0(k1_enumset1(A_78, B_79, C_80), k1_tarski(D_81))=k2_enumset1(A_78, B_79, C_80, D_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.20  tff(c_127, plain, (![A_35, B_36, D_81]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_81))=k2_enumset1(A_35, A_35, B_36, D_81))), inference(superposition, [status(thm), theory('equality')], [c_18, c_118])).
% 2.01/1.20  tff(c_140, plain, (![A_87, B_88, D_89]: (k2_xboole_0(k2_tarski(A_87, B_88), k1_tarski(D_89))=k1_enumset1(A_87, B_88, D_89))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_127])).
% 2.01/1.20  tff(c_168, plain, (![B_92, A_93, D_94]: (k2_xboole_0(k2_tarski(B_92, A_93), k1_tarski(D_94))=k1_enumset1(A_93, B_92, D_94))), inference(superposition, [status(thm), theory('equality')], [c_6, c_140])).
% 2.01/1.20  tff(c_130, plain, (![A_35, B_36, D_81]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_81))=k1_enumset1(A_35, B_36, D_81))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_127])).
% 2.01/1.20  tff(c_174, plain, (![B_92, A_93, D_94]: (k1_enumset1(B_92, A_93, D_94)=k1_enumset1(A_93, B_92, D_94))), inference(superposition, [status(thm), theory('equality')], [c_168, c_130])).
% 2.01/1.20  tff(c_30, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.01/1.20  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_174, c_30])).
% 2.01/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.20  
% 2.01/1.20  Inference rules
% 2.01/1.20  ----------------------
% 2.01/1.20  #Ref     : 0
% 2.01/1.20  #Sup     : 39
% 2.01/1.20  #Fact    : 0
% 2.01/1.20  #Define  : 0
% 2.01/1.20  #Split   : 0
% 2.01/1.20  #Chain   : 0
% 2.01/1.20  #Close   : 0
% 2.01/1.20  
% 2.01/1.20  Ordering : KBO
% 2.01/1.20  
% 2.01/1.20  Simplification rules
% 2.01/1.20  ----------------------
% 2.01/1.20  #Subsume      : 0
% 2.01/1.21  #Demod        : 7
% 2.01/1.21  #Tautology    : 33
% 2.01/1.21  #SimpNegUnit  : 0
% 2.01/1.21  #BackRed      : 1
% 2.01/1.21  
% 2.01/1.21  #Partial instantiations: 0
% 2.01/1.21  #Strategies tried      : 1
% 2.01/1.21  
% 2.01/1.21  Timing (in seconds)
% 2.01/1.21  ----------------------
% 2.01/1.21  Preprocessing        : 0.31
% 2.01/1.21  Parsing              : 0.16
% 2.01/1.21  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.14
% 2.01/1.21  Inferencing          : 0.05
% 2.01/1.21  Reduction            : 0.05
% 2.01/1.21  Demodulation         : 0.04
% 2.01/1.21  BG Simplification    : 0.02
% 2.01/1.21  Subsumption          : 0.02
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.47
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
