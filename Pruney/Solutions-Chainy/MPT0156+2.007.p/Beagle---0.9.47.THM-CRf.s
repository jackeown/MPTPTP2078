%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_tarski(D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_37,E_36,D_34,B_35,C_38] : k2_xboole_0(k2_enumset1(A_37,B_35,C_38,D_34),k1_tarski(E_36)) = k3_enumset1(A_37,B_35,C_38,D_34,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_19,B_20,C_21,E_36] : k3_enumset1(A_19,A_19,B_20,C_21,E_36) = k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(E_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_71,plain,(
    ! [A_19,B_20,C_21,E_36] : k3_enumset1(A_19,A_19,B_20,C_21,E_36) = k2_enumset1(A_19,B_20,C_21,E_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_14,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:47:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.63/1.17  
% 1.63/1.17  %Foreground sorts:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Background operators:
% 1.63/1.17  
% 1.63/1.17  
% 1.63/1.17  %Foreground operators:
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.63/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.63/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.63/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.17  
% 1.63/1.17  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.63/1.17  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.63/1.17  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.63/1.17  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.63/1.17  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_tarski(D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.17  tff(c_12, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.17  tff(c_59, plain, (![A_37, E_36, D_34, B_35, C_38]: (k2_xboole_0(k2_enumset1(A_37, B_35, C_38, D_34), k1_tarski(E_36))=k3_enumset1(A_37, B_35, C_38, D_34, E_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.17  tff(c_68, plain, (![A_19, B_20, C_21, E_36]: (k3_enumset1(A_19, A_19, B_20, C_21, E_36)=k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(E_36)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_59])).
% 1.63/1.17  tff(c_71, plain, (![A_19, B_20, C_21, E_36]: (k3_enumset1(A_19, A_19, B_20, C_21, E_36)=k2_enumset1(A_19, B_20, C_21, E_36))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_68])).
% 1.63/1.17  tff(c_14, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.63/1.17  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_14])).
% 1.63/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  Inference rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Ref     : 0
% 1.63/1.17  #Sup     : 21
% 1.63/1.17  #Fact    : 0
% 1.63/1.17  #Define  : 0
% 1.63/1.17  #Split   : 0
% 1.63/1.17  #Chain   : 0
% 1.63/1.17  #Close   : 0
% 1.63/1.17  
% 1.63/1.17  Ordering : KBO
% 1.63/1.17  
% 1.63/1.17  Simplification rules
% 1.63/1.17  ----------------------
% 1.63/1.17  #Subsume      : 0
% 1.63/1.17  #Demod        : 4
% 1.63/1.17  #Tautology    : 17
% 1.63/1.17  #SimpNegUnit  : 0
% 1.63/1.17  #BackRed      : 1
% 1.63/1.17  
% 1.63/1.17  #Partial instantiations: 0
% 1.63/1.17  #Strategies tried      : 1
% 1.63/1.17  
% 1.63/1.17  Timing (in seconds)
% 1.63/1.17  ----------------------
% 1.63/1.18  Preprocessing        : 0.28
% 1.63/1.18  Parsing              : 0.15
% 1.63/1.18  CNF conversion       : 0.02
% 1.63/1.18  Main loop            : 0.10
% 1.63/1.18  Inferencing          : 0.04
% 1.63/1.18  Reduction            : 0.03
% 1.63/1.18  Demodulation         : 0.02
% 1.63/1.18  BG Simplification    : 0.01
% 1.63/1.18  Subsumption          : 0.01
% 1.63/1.18  Abstraction          : 0.01
% 1.63/1.18  MUC search           : 0.00
% 1.63/1.18  Cooper               : 0.00
% 1.63/1.18  Total                : 0.39
% 1.63/1.18  Index Insertion      : 0.00
% 1.63/1.18  Index Deletion       : 0.00
% 1.63/1.18  Index Matching       : 0.00
% 1.63/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
