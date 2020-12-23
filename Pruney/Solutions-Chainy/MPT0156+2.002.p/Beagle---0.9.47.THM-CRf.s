%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :   15 (  16 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_xboole_0(k1_tarski(A_35),k1_enumset1(B_36,C_37,D_38)) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_1,C_30] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_30)) = k2_xboole_0(A_1,C_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_53])).

tff(c_196,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_xboole_0(k1_tarski(A_35),k2_enumset1(A_35,B_36,C_37,D_38)) = k2_xboole_0(k1_tarski(A_35),k1_enumset1(B_36,C_37,D_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_72])).

tff(c_1222,plain,(
    ! [A_91,B_92,C_93,D_94] : k2_xboole_0(k1_tarski(A_91),k2_enumset1(A_91,B_92,C_93,D_94)) = k2_enumset1(A_91,B_92,C_93,D_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_196])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1228,plain,(
    ! [A_91,B_92,C_93,D_94] : k3_enumset1(A_91,A_91,B_92,C_93,D_94) = k2_enumset1(A_91,B_92,C_93,D_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_8])).

tff(c_16,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.77/1.43  
% 2.77/1.43  %Foreground sorts:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Background operators:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Foreground operators:
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.43  
% 2.77/1.44  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.77/1.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.77/1.44  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.77/1.44  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.77/1.44  tff(f_42, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.77/1.44  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.44  tff(c_187, plain, (![A_35, B_36, C_37, D_38]: (k2_xboole_0(k1_tarski(A_35), k1_enumset1(B_36, C_37, D_38))=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.44  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.44  tff(c_53, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.44  tff(c_72, plain, (![A_1, C_30]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_30))=k2_xboole_0(A_1, C_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_53])).
% 2.77/1.44  tff(c_196, plain, (![A_35, B_36, C_37, D_38]: (k2_xboole_0(k1_tarski(A_35), k2_enumset1(A_35, B_36, C_37, D_38))=k2_xboole_0(k1_tarski(A_35), k1_enumset1(B_36, C_37, D_38)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_72])).
% 2.77/1.44  tff(c_1222, plain, (![A_91, B_92, C_93, D_94]: (k2_xboole_0(k1_tarski(A_91), k2_enumset1(A_91, B_92, C_93, D_94))=k2_enumset1(A_91, B_92, C_93, D_94))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_196])).
% 2.77/1.44  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k1_tarski(A_10), k2_enumset1(B_11, C_12, D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.44  tff(c_1228, plain, (![A_91, B_92, C_93, D_94]: (k3_enumset1(A_91, A_91, B_92, C_93, D_94)=k2_enumset1(A_91, B_92, C_93, D_94))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_8])).
% 2.77/1.44  tff(c_16, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.44  tff(c_1270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1228, c_16])).
% 2.77/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  Inference rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Ref     : 0
% 2.77/1.44  #Sup     : 292
% 2.77/1.44  #Fact    : 0
% 2.77/1.44  #Define  : 0
% 2.77/1.44  #Split   : 0
% 2.77/1.44  #Chain   : 0
% 2.77/1.44  #Close   : 0
% 2.77/1.44  
% 2.77/1.44  Ordering : KBO
% 2.77/1.44  
% 2.77/1.44  Simplification rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Subsume      : 15
% 2.77/1.44  #Demod        : 320
% 2.77/1.44  #Tautology    : 207
% 2.77/1.44  #SimpNegUnit  : 0
% 2.77/1.44  #BackRed      : 1
% 2.77/1.44  
% 2.77/1.44  #Partial instantiations: 0
% 2.77/1.44  #Strategies tried      : 1
% 2.77/1.44  
% 2.77/1.44  Timing (in seconds)
% 2.77/1.44  ----------------------
% 2.77/1.44  Preprocessing        : 0.28
% 2.77/1.44  Parsing              : 0.15
% 2.77/1.44  CNF conversion       : 0.02
% 2.77/1.44  Main loop            : 0.40
% 2.77/1.44  Inferencing          : 0.16
% 2.77/1.44  Reduction            : 0.16
% 2.77/1.44  Demodulation         : 0.14
% 2.77/1.44  BG Simplification    : 0.02
% 2.77/1.44  Subsumption          : 0.04
% 2.77/1.44  Abstraction          : 0.03
% 2.77/1.44  MUC search           : 0.00
% 2.77/1.44  Cooper               : 0.00
% 2.77/1.44  Total                : 0.70
% 2.77/1.44  Index Insertion      : 0.00
% 2.77/1.44  Index Deletion       : 0.00
% 2.77/1.44  Index Matching       : 0.00
% 2.77/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
