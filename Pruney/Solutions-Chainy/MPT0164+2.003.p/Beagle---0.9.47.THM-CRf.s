%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:25 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_37,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k1_tarski(A_1),k2_enumset1(B_2,C_3,D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_31] : k1_enumset1(A_31,A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_57,E_61,C_56,G_62,F_59,B_58,D_60] : k2_xboole_0(k1_enumset1(A_57,B_58,C_56),k2_enumset1(D_60,E_61,F_59,G_62)) = k5_enumset1(A_57,B_58,C_56,D_60,E_61,F_59,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [E_61,A_31,G_62,F_59,D_60] : k5_enumset1(A_31,A_31,A_31,D_60,E_61,F_59,G_62) = k2_xboole_0(k1_tarski(A_31),k2_enumset1(D_60,E_61,F_59,G_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_60])).

tff(c_72,plain,(
    ! [E_61,A_31,G_62,F_59,D_60] : k5_enumset1(A_31,A_31,A_31,D_60,E_61,F_59,G_62) = k3_enumset1(A_31,D_60,E_61,F_59,G_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_14,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.12  
% 1.75/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.13  
% 1.75/1.13  %Foreground sorts:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Background operators:
% 1.75/1.13  
% 1.75/1.13  
% 1.75/1.13  %Foreground operators:
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.75/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.75/1.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.75/1.13  
% 1.75/1.13  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.75/1.13  tff(f_37, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 1.75/1.13  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 1.75/1.13  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 1.75/1.13  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k1_tarski(A_1), k2_enumset1(B_2, C_3, D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.75/1.13  tff(c_12, plain, (![A_31]: (k1_enumset1(A_31, A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.13  tff(c_60, plain, (![A_57, E_61, C_56, G_62, F_59, B_58, D_60]: (k2_xboole_0(k1_enumset1(A_57, B_58, C_56), k2_enumset1(D_60, E_61, F_59, G_62))=k5_enumset1(A_57, B_58, C_56, D_60, E_61, F_59, G_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.13  tff(c_69, plain, (![E_61, A_31, G_62, F_59, D_60]: (k5_enumset1(A_31, A_31, A_31, D_60, E_61, F_59, G_62)=k2_xboole_0(k1_tarski(A_31), k2_enumset1(D_60, E_61, F_59, G_62)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_60])).
% 1.75/1.13  tff(c_72, plain, (![E_61, A_31, G_62, F_59, D_60]: (k5_enumset1(A_31, A_31, A_31, D_60, E_61, F_59, G_62)=k3_enumset1(A_31, D_60, E_61, F_59, G_62))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_69])).
% 1.75/1.13  tff(c_14, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.75/1.13  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_14])).
% 1.75/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.13  
% 1.75/1.13  Inference rules
% 1.75/1.13  ----------------------
% 1.75/1.13  #Ref     : 0
% 1.75/1.13  #Sup     : 13
% 1.75/1.13  #Fact    : 0
% 1.75/1.13  #Define  : 0
% 1.75/1.13  #Split   : 0
% 1.75/1.13  #Chain   : 0
% 1.75/1.13  #Close   : 0
% 1.75/1.13  
% 1.75/1.13  Ordering : KBO
% 1.75/1.13  
% 1.75/1.13  Simplification rules
% 1.75/1.13  ----------------------
% 1.75/1.13  #Subsume      : 0
% 1.75/1.13  #Demod        : 2
% 1.75/1.13  #Tautology    : 12
% 1.75/1.13  #SimpNegUnit  : 0
% 1.75/1.13  #BackRed      : 1
% 1.75/1.13  
% 1.75/1.13  #Partial instantiations: 0
% 1.75/1.13  #Strategies tried      : 1
% 1.75/1.13  
% 1.75/1.13  Timing (in seconds)
% 1.75/1.13  ----------------------
% 1.75/1.14  Preprocessing        : 0.29
% 1.75/1.14  Parsing              : 0.15
% 1.75/1.14  CNF conversion       : 0.02
% 1.75/1.14  Main loop            : 0.09
% 1.75/1.14  Inferencing          : 0.04
% 1.75/1.14  Reduction            : 0.03
% 1.75/1.14  Demodulation         : 0.02
% 1.75/1.14  BG Simplification    : 0.01
% 1.75/1.14  Subsumption          : 0.01
% 1.75/1.14  Abstraction          : 0.01
% 1.75/1.14  MUC search           : 0.00
% 1.75/1.14  Cooper               : 0.00
% 1.75/1.14  Total                : 0.41
% 1.75/1.14  Index Insertion      : 0.00
% 1.75/1.14  Index Deletion       : 0.00
% 1.75/1.14  Index Matching       : 0.00
% 1.86/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
