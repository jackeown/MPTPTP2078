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
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_4,plain,(
    ! [D_10,A_7,B_8,E_11,C_9] : k2_xboole_0(k2_tarski(A_7,B_8),k1_enumset1(C_9,D_10,E_11)) = k3_enumset1(A_7,B_8,C_9,D_10,E_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [C_39,B_38,D_37,E_36,A_40,F_35] : k2_xboole_0(k1_enumset1(A_40,B_38,C_39),k1_enumset1(D_37,E_36,F_35)) = k4_enumset1(A_40,B_38,C_39,D_37,E_36,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [D_37,E_36,A_12,B_13,F_35] : k4_enumset1(A_12,A_12,B_13,D_37,E_36,F_35) = k2_xboole_0(k2_tarski(A_12,B_13),k1_enumset1(D_37,E_36,F_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_67,plain,(
    ! [D_37,E_36,A_12,B_13,F_35] : k4_enumset1(A_12,A_12,B_13,D_37,E_36,F_35) = k3_enumset1(A_12,B_13,D_37,E_36,F_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_12,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.23  
% 1.79/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.23  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.79/1.23  
% 1.79/1.23  %Foreground sorts:
% 1.79/1.23  
% 1.79/1.23  
% 1.79/1.23  %Background operators:
% 1.79/1.23  
% 1.79/1.23  
% 1.79/1.23  %Foreground operators:
% 1.79/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.23  
% 1.79/1.24  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.79/1.24  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.79/1.24  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 1.79/1.24  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.79/1.24  tff(c_4, plain, (![D_10, A_7, B_8, E_11, C_9]: (k2_xboole_0(k2_tarski(A_7, B_8), k1_enumset1(C_9, D_10, E_11))=k3_enumset1(A_7, B_8, C_9, D_10, E_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.24  tff(c_6, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.24  tff(c_52, plain, (![C_39, B_38, D_37, E_36, A_40, F_35]: (k2_xboole_0(k1_enumset1(A_40, B_38, C_39), k1_enumset1(D_37, E_36, F_35))=k4_enumset1(A_40, B_38, C_39, D_37, E_36, F_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.24  tff(c_61, plain, (![D_37, E_36, A_12, B_13, F_35]: (k4_enumset1(A_12, A_12, B_13, D_37, E_36, F_35)=k2_xboole_0(k2_tarski(A_12, B_13), k1_enumset1(D_37, E_36, F_35)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 1.79/1.24  tff(c_67, plain, (![D_37, E_36, A_12, B_13, F_35]: (k4_enumset1(A_12, A_12, B_13, D_37, E_36, F_35)=k3_enumset1(A_12, B_13, D_37, E_36, F_35))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 1.79/1.24  tff(c_12, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.24  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_12])).
% 1.79/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.24  
% 1.79/1.24  Inference rules
% 1.79/1.24  ----------------------
% 1.79/1.24  #Ref     : 0
% 1.79/1.24  #Sup     : 30
% 1.79/1.24  #Fact    : 0
% 1.79/1.24  #Define  : 0
% 1.79/1.24  #Split   : 0
% 1.79/1.24  #Chain   : 0
% 1.79/1.24  #Close   : 0
% 1.79/1.24  
% 1.79/1.24  Ordering : KBO
% 1.79/1.24  
% 1.79/1.24  Simplification rules
% 1.79/1.24  ----------------------
% 1.79/1.24  #Subsume      : 1
% 1.79/1.24  #Demod        : 4
% 1.79/1.24  #Tautology    : 24
% 1.79/1.24  #SimpNegUnit  : 0
% 1.79/1.24  #BackRed      : 1
% 1.79/1.24  
% 1.79/1.24  #Partial instantiations: 0
% 1.79/1.24  #Strategies tried      : 1
% 1.79/1.24  
% 1.79/1.24  Timing (in seconds)
% 1.79/1.24  ----------------------
% 1.79/1.24  Preprocessing        : 0.29
% 1.79/1.24  Parsing              : 0.16
% 1.79/1.24  CNF conversion       : 0.02
% 1.79/1.24  Main loop            : 0.12
% 1.79/1.24  Inferencing          : 0.06
% 1.79/1.24  Reduction            : 0.04
% 1.79/1.24  Demodulation         : 0.03
% 1.79/1.24  BG Simplification    : 0.01
% 1.79/1.24  Subsumption          : 0.01
% 1.79/1.24  Abstraction          : 0.01
% 1.79/1.24  MUC search           : 0.00
% 1.79/1.24  Cooper               : 0.00
% 1.79/1.24  Total                : 0.43
% 1.79/1.24  Index Insertion      : 0.00
% 1.79/1.24  Index Deletion       : 0.00
% 1.79/1.24  Index Matching       : 0.00
% 1.79/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
