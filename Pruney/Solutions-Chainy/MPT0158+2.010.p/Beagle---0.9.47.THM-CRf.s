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
% DateTime   : Thu Dec  3 09:46:19 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] : k2_xboole_0(k3_enumset1(A_5,B_6,C_7,D_8,E_9),k1_tarski(F_10)) = k4_enumset1(A_5,B_6,C_7,D_8,E_9,F_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [C_30,E_32,D_31,B_29,A_28] : k4_enumset1(A_28,A_28,B_29,C_30,D_31,E_32) = k3_enumset1(A_28,B_29,C_30,D_31,E_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_97,plain,(
    ! [D_63,A_61,B_62,G_60,F_58,C_59,E_64] : k2_xboole_0(k4_enumset1(A_61,B_62,C_59,D_63,E_64,F_58),k1_tarski(G_60)) = k5_enumset1(A_61,B_62,C_59,D_63,E_64,F_58,G_60) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [C_30,G_60,E_32,D_31,B_29,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,G_60) = k2_xboole_0(k3_enumset1(A_28,B_29,C_30,D_31,E_32),k1_tarski(G_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_109,plain,(
    ! [C_30,G_60,E_32,D_31,B_29,A_28] : k5_enumset1(A_28,A_28,B_29,C_30,D_31,E_32,G_60) = k4_enumset1(A_28,B_29,C_30,D_31,E_32,G_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_20,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.67/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.67/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.14  
% 1.67/1.14  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 1.67/1.14  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.67/1.14  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 1.67/1.14  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.67/1.14  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (k2_xboole_0(k3_enumset1(A_5, B_6, C_7, D_8, E_9), k1_tarski(F_10))=k4_enumset1(A_5, B_6, C_7, D_8, E_9, F_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_18, plain, (![C_30, E_32, D_31, B_29, A_28]: (k4_enumset1(A_28, A_28, B_29, C_30, D_31, E_32)=k3_enumset1(A_28, B_29, C_30, D_31, E_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.14  tff(c_97, plain, (![D_63, A_61, B_62, G_60, F_58, C_59, E_64]: (k2_xboole_0(k4_enumset1(A_61, B_62, C_59, D_63, E_64, F_58), k1_tarski(G_60))=k5_enumset1(A_61, B_62, C_59, D_63, E_64, F_58, G_60))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.14  tff(c_106, plain, (![C_30, G_60, E_32, D_31, B_29, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, G_60)=k2_xboole_0(k3_enumset1(A_28, B_29, C_30, D_31, E_32), k1_tarski(G_60)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_97])).
% 1.67/1.14  tff(c_109, plain, (![C_30, G_60, E_32, D_31, B_29, A_28]: (k5_enumset1(A_28, A_28, B_29, C_30, D_31, E_32, G_60)=k4_enumset1(A_28, B_29, C_30, D_31, E_32, G_60))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_106])).
% 1.67/1.14  tff(c_20, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.14  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_20])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 31
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 6
% 1.67/1.14  #Tautology    : 26
% 1.67/1.14  #SimpNegUnit  : 0
% 1.67/1.14  #BackRed      : 1
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.15  Preprocessing        : 0.28
% 1.67/1.15  Parsing              : 0.15
% 1.67/1.15  CNF conversion       : 0.02
% 1.67/1.15  Main loop            : 0.11
% 1.67/1.15  Inferencing          : 0.05
% 1.67/1.15  Reduction            : 0.04
% 1.67/1.15  Demodulation         : 0.03
% 1.67/1.15  BG Simplification    : 0.01
% 1.67/1.15  Subsumption          : 0.01
% 1.67/1.15  Abstraction          : 0.01
% 1.67/1.15  MUC search           : 0.00
% 1.67/1.15  Cooper               : 0.00
% 1.67/1.15  Total                : 0.41
% 1.67/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
