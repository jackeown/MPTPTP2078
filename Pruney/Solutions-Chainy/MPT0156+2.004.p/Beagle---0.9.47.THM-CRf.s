%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:14 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [D_63,A_66,B_64,C_65,E_67] : k2_xboole_0(k1_enumset1(A_66,B_64,C_65),k2_tarski(D_63,E_67)) = k3_enumset1(A_66,B_64,C_65,D_63,E_67) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_40,B_41,D_63,E_67] : k3_enumset1(A_40,A_40,B_41,D_63,E_67) = k2_xboole_0(k2_tarski(A_40,B_41),k2_tarski(D_63,E_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_148,plain,(
    ! [A_40,B_41,D_63,E_67] : k3_enumset1(A_40,A_40,B_41,D_63,E_67) = k2_enumset1(A_40,B_41,D_63,E_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_142])).

tff(c_22,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.17  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.17  
% 1.91/1.17  %Foreground sorts:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Background operators:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Foreground operators:
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.17  
% 1.91/1.17  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.91/1.17  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.91/1.17  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 1.91/1.17  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.91/1.17  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.17  tff(c_18, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.17  tff(c_130, plain, (![D_63, A_66, B_64, C_65, E_67]: (k2_xboole_0(k1_enumset1(A_66, B_64, C_65), k2_tarski(D_63, E_67))=k3_enumset1(A_66, B_64, C_65, D_63, E_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.17  tff(c_142, plain, (![A_40, B_41, D_63, E_67]: (k3_enumset1(A_40, A_40, B_41, D_63, E_67)=k2_xboole_0(k2_tarski(A_40, B_41), k2_tarski(D_63, E_67)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_130])).
% 1.91/1.17  tff(c_148, plain, (![A_40, B_41, D_63, E_67]: (k3_enumset1(A_40, A_40, B_41, D_63, E_67)=k2_enumset1(A_40, B_41, D_63, E_67))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_142])).
% 1.91/1.17  tff(c_22, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.17  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_22])).
% 1.91/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  Inference rules
% 1.91/1.17  ----------------------
% 1.91/1.17  #Ref     : 0
% 1.91/1.17  #Sup     : 39
% 1.91/1.17  #Fact    : 0
% 1.91/1.17  #Define  : 0
% 1.91/1.17  #Split   : 0
% 1.91/1.17  #Chain   : 0
% 1.91/1.17  #Close   : 0
% 1.91/1.17  
% 1.91/1.17  Ordering : KBO
% 1.91/1.17  
% 1.91/1.17  Simplification rules
% 1.91/1.17  ----------------------
% 1.91/1.17  #Subsume      : 0
% 1.91/1.17  #Demod        : 12
% 1.91/1.17  #Tautology    : 30
% 1.91/1.17  #SimpNegUnit  : 0
% 1.91/1.17  #BackRed      : 1
% 1.91/1.17  
% 1.91/1.17  #Partial instantiations: 0
% 1.91/1.17  #Strategies tried      : 1
% 1.91/1.17  
% 1.91/1.17  Timing (in seconds)
% 1.91/1.17  ----------------------
% 1.91/1.18  Preprocessing        : 0.29
% 1.91/1.18  Parsing              : 0.15
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.12
% 1.91/1.18  Inferencing          : 0.05
% 1.91/1.18  Reduction            : 0.04
% 1.91/1.18  Demodulation         : 0.04
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.01
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.43
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.18  Index Matching       : 0.00
% 1.91/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
