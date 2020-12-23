%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:19 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] : k2_xboole_0(k2_enumset1(A_5,B_6,C_7,D_8),k2_tarski(E_9,F_10)) = k4_enumset1(A_5,B_6,C_7,D_8,E_9,F_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [D_66,C_62,F_61,A_64,E_67,B_65,G_63] : k2_xboole_0(k3_enumset1(A_64,B_65,C_62,D_66,E_67),k2_tarski(F_61,G_63)) = k5_enumset1(A_64,B_65,C_62,D_66,E_67,F_61,G_63) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_23,B_24,F_61,D_26,C_25,G_63] : k5_enumset1(A_23,A_23,B_24,C_25,D_26,F_61,G_63) = k2_xboole_0(k2_enumset1(A_23,B_24,C_25,D_26),k2_tarski(F_61,G_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_99])).

tff(c_111,plain,(
    ! [A_23,B_24,F_61,D_26,C_25,G_63] : k5_enumset1(A_23,A_23,B_24,C_25,D_26,F_61,G_63) = k4_enumset1(A_23,B_24,C_25,D_26,F_61,G_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_18,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:40:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.71/1.11  
% 1.71/1.11  %Foreground sorts:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Background operators:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Foreground operators:
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.11  tff('#skF_6', type, '#skF_6': $i).
% 1.71/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.11  
% 1.71/1.11  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 1.71/1.11  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.71/1.11  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 1.71/1.11  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.71/1.11  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (k2_xboole_0(k2_enumset1(A_5, B_6, C_7, D_8), k2_tarski(E_9, F_10))=k4_enumset1(A_5, B_6, C_7, D_8, E_9, F_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.11  tff(c_14, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.11  tff(c_99, plain, (![D_66, C_62, F_61, A_64, E_67, B_65, G_63]: (k2_xboole_0(k3_enumset1(A_64, B_65, C_62, D_66, E_67), k2_tarski(F_61, G_63))=k5_enumset1(A_64, B_65, C_62, D_66, E_67, F_61, G_63))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.11  tff(c_108, plain, (![A_23, B_24, F_61, D_26, C_25, G_63]: (k5_enumset1(A_23, A_23, B_24, C_25, D_26, F_61, G_63)=k2_xboole_0(k2_enumset1(A_23, B_24, C_25, D_26), k2_tarski(F_61, G_63)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_99])).
% 1.71/1.11  tff(c_111, plain, (![A_23, B_24, F_61, D_26, C_25, G_63]: (k5_enumset1(A_23, A_23, B_24, C_25, D_26, F_61, G_63)=k4_enumset1(A_23, B_24, C_25, D_26, F_61, G_63))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_108])).
% 1.71/1.11  tff(c_18, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.11  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_18])).
% 1.71/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  Inference rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Ref     : 0
% 1.71/1.11  #Sup     : 23
% 1.71/1.11  #Fact    : 0
% 1.71/1.11  #Define  : 0
% 1.71/1.11  #Split   : 0
% 1.71/1.11  #Chain   : 0
% 1.71/1.11  #Close   : 0
% 1.71/1.11  
% 1.71/1.11  Ordering : KBO
% 1.71/1.11  
% 1.71/1.11  Simplification rules
% 1.71/1.11  ----------------------
% 1.71/1.11  #Subsume      : 0
% 1.71/1.11  #Demod        : 4
% 1.71/1.11  #Tautology    : 20
% 1.71/1.11  #SimpNegUnit  : 0
% 1.71/1.11  #BackRed      : 1
% 1.71/1.11  
% 1.71/1.11  #Partial instantiations: 0
% 1.71/1.11  #Strategies tried      : 1
% 1.71/1.11  
% 1.71/1.11  Timing (in seconds)
% 1.71/1.11  ----------------------
% 1.71/1.12  Preprocessing        : 0.28
% 1.71/1.12  Parsing              : 0.15
% 1.71/1.12  CNF conversion       : 0.02
% 1.71/1.12  Main loop            : 0.10
% 1.71/1.12  Inferencing          : 0.05
% 1.71/1.12  Reduction            : 0.03
% 1.71/1.12  Demodulation         : 0.02
% 1.71/1.12  BG Simplification    : 0.01
% 1.71/1.12  Subsumption          : 0.01
% 1.71/1.12  Abstraction          : 0.01
% 1.71/1.12  MUC search           : 0.00
% 1.71/1.12  Cooper               : 0.00
% 1.71/1.12  Total                : 0.40
% 1.71/1.12  Index Insertion      : 0.00
% 1.71/1.12  Index Deletion       : 0.00
% 1.71/1.12  Index Matching       : 0.00
% 1.71/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
