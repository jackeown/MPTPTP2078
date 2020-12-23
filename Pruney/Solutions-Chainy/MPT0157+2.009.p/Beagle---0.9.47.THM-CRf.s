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
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
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
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k1_tarski(A_1),k2_enumset1(B_2,C_3,D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [B_38,D_39,E_40,A_37,C_36,F_35] : k2_xboole_0(k2_tarski(A_37,B_38),k2_enumset1(C_36,D_39,E_40,F_35)) = k4_enumset1(A_37,B_38,C_36,D_39,E_40,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [D_39,E_40,A_23,C_36,F_35] : k4_enumset1(A_23,A_23,C_36,D_39,E_40,F_35) = k2_xboole_0(k1_tarski(A_23),k2_enumset1(C_36,D_39,E_40,F_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_52,plain,(
    ! [D_39,E_40,A_23,C_36,F_35] : k4_enumset1(A_23,A_23,C_36,D_39,E_40,F_35) = k3_enumset1(A_23,C_36,D_39,E_40,F_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_12,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.13  
% 1.53/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.13  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.53/1.13  
% 1.53/1.13  %Foreground sorts:
% 1.53/1.13  
% 1.53/1.13  
% 1.53/1.13  %Background operators:
% 1.53/1.13  
% 1.53/1.13  
% 1.53/1.13  %Foreground operators:
% 1.53/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.53/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.53/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.53/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.53/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.53/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.53/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.53/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.53/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.53/1.13  
% 1.53/1.14  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.53/1.14  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.53/1.14  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 1.53/1.14  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.53/1.14  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k1_tarski(A_1), k2_enumset1(B_2, C_3, D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.14  tff(c_10, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.53/1.14  tff(c_40, plain, (![B_38, D_39, E_40, A_37, C_36, F_35]: (k2_xboole_0(k2_tarski(A_37, B_38), k2_enumset1(C_36, D_39, E_40, F_35))=k4_enumset1(A_37, B_38, C_36, D_39, E_40, F_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.53/1.14  tff(c_49, plain, (![D_39, E_40, A_23, C_36, F_35]: (k4_enumset1(A_23, A_23, C_36, D_39, E_40, F_35)=k2_xboole_0(k1_tarski(A_23), k2_enumset1(C_36, D_39, E_40, F_35)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_40])).
% 1.53/1.14  tff(c_52, plain, (![D_39, E_40, A_23, C_36, F_35]: (k4_enumset1(A_23, A_23, C_36, D_39, E_40, F_35)=k3_enumset1(A_23, C_36, D_39, E_40, F_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_49])).
% 1.53/1.14  tff(c_12, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.53/1.14  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_12])).
% 1.53/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.14  
% 1.53/1.14  Inference rules
% 1.53/1.14  ----------------------
% 1.53/1.14  #Ref     : 0
% 1.53/1.14  #Sup     : 11
% 1.53/1.14  #Fact    : 0
% 1.53/1.14  #Define  : 0
% 1.53/1.14  #Split   : 0
% 1.53/1.14  #Chain   : 0
% 1.53/1.14  #Close   : 0
% 1.53/1.14  
% 1.53/1.14  Ordering : KBO
% 1.53/1.14  
% 1.53/1.14  Simplification rules
% 1.53/1.14  ----------------------
% 1.53/1.14  #Subsume      : 0
% 1.53/1.14  #Demod        : 2
% 1.53/1.14  #Tautology    : 10
% 1.53/1.14  #SimpNegUnit  : 0
% 1.53/1.14  #BackRed      : 1
% 1.53/1.14  
% 1.53/1.14  #Partial instantiations: 0
% 1.53/1.14  #Strategies tried      : 1
% 1.53/1.14  
% 1.53/1.14  Timing (in seconds)
% 1.53/1.14  ----------------------
% 1.53/1.14  Preprocessing        : 0.28
% 1.53/1.14  Parsing              : 0.15
% 1.53/1.14  CNF conversion       : 0.02
% 1.53/1.14  Main loop            : 0.08
% 1.53/1.14  Inferencing          : 0.04
% 1.53/1.14  Reduction            : 0.02
% 1.53/1.14  Demodulation         : 0.02
% 1.53/1.14  BG Simplification    : 0.01
% 1.53/1.14  Subsumption          : 0.01
% 1.53/1.14  Abstraction          : 0.01
% 1.53/1.14  MUC search           : 0.00
% 1.53/1.14  Cooper               : 0.00
% 1.53/1.14  Total                : 0.38
% 1.53/1.14  Index Insertion      : 0.00
% 1.53/1.14  Index Deletion       : 0.00
% 1.53/1.14  Index Matching       : 0.00
% 1.53/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
