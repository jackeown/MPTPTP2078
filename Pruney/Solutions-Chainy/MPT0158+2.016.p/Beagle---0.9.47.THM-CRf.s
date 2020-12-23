%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_4,plain,(
    ! [D_10,A_7,F_12,B_8,E_11,C_9] : k2_xboole_0(k3_enumset1(A_7,B_8,C_9,D_10,E_11),k1_tarski(F_12)) = k4_enumset1(A_7,B_8,C_9,D_10,E_11,F_12) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] : k4_enumset1(A_20,A_20,B_21,C_22,D_23,E_24) = k3_enumset1(A_20,B_21,C_22,D_23,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_46,F_42,C_48,G_47,D_43,E_45,B_44] : k2_xboole_0(k4_enumset1(A_46,B_44,C_48,D_43,E_45,F_42),k1_tarski(G_47)) = k5_enumset1(A_46,B_44,C_48,D_43,E_45,F_42,G_47) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [C_22,D_23,A_20,B_21,E_24,G_47] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,E_24,G_47) = k2_xboole_0(k3_enumset1(A_20,B_21,C_22,D_23,E_24),k1_tarski(G_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_50,plain,(
    ! [C_22,D_23,A_20,B_21,E_24,G_47] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,E_24,G_47) = k4_enumset1(A_20,B_21,C_22,D_23,E_24,G_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.66/1.13  
% 1.66/1.13  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 1.66/1.13  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.66/1.13  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 1.66/1.13  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.66/1.13  tff(c_4, plain, (![D_10, A_7, F_12, B_8, E_11, C_9]: (k2_xboole_0(k3_enumset1(A_7, B_8, C_9, D_10, E_11), k1_tarski(F_12))=k4_enumset1(A_7, B_8, C_9, D_10, E_11, F_12))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.13  tff(c_8, plain, (![C_22, D_23, A_20, B_21, E_24]: (k4_enumset1(A_20, A_20, B_21, C_22, D_23, E_24)=k3_enumset1(A_20, B_21, C_22, D_23, E_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.13  tff(c_38, plain, (![A_46, F_42, C_48, G_47, D_43, E_45, B_44]: (k2_xboole_0(k4_enumset1(A_46, B_44, C_48, D_43, E_45, F_42), k1_tarski(G_47))=k5_enumset1(A_46, B_44, C_48, D_43, E_45, F_42, G_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.13  tff(c_47, plain, (![C_22, D_23, A_20, B_21, E_24, G_47]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, G_47)=k2_xboole_0(k3_enumset1(A_20, B_21, C_22, D_23, E_24), k1_tarski(G_47)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 1.66/1.13  tff(c_50, plain, (![C_22, D_23, A_20, B_21, E_24, G_47]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, G_47)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, G_47))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 1.66/1.13  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.66/1.13  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 1.66/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  Inference rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Ref     : 0
% 1.66/1.13  #Sup     : 9
% 1.66/1.13  #Fact    : 0
% 1.66/1.13  #Define  : 0
% 1.66/1.13  #Split   : 0
% 1.66/1.13  #Chain   : 0
% 1.66/1.13  #Close   : 0
% 1.66/1.13  
% 1.66/1.13  Ordering : KBO
% 1.66/1.13  
% 1.66/1.13  Simplification rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Subsume      : 0
% 1.66/1.13  #Demod        : 2
% 1.66/1.13  #Tautology    : 8
% 1.66/1.13  #SimpNegUnit  : 0
% 1.66/1.13  #BackRed      : 1
% 1.66/1.13  
% 1.66/1.13  #Partial instantiations: 0
% 1.66/1.13  #Strategies tried      : 1
% 1.66/1.13  
% 1.66/1.13  Timing (in seconds)
% 1.66/1.13  ----------------------
% 1.66/1.14  Preprocessing        : 0.27
% 1.66/1.14  Parsing              : 0.14
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.07
% 1.66/1.14  Inferencing          : 0.04
% 1.66/1.14  Reduction            : 0.02
% 1.66/1.14  Demodulation         : 0.02
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.01
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.36
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
