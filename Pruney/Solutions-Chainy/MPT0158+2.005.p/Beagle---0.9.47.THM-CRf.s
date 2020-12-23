%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:19 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
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
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_enumset1(D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_21,B_22,C_23] : k2_enumset1(A_21,A_21,B_22,C_23) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [C_42,F_45,D_40,E_46,G_44,A_43,B_41] : k2_xboole_0(k2_enumset1(A_43,B_41,C_42,D_40),k1_enumset1(E_46,F_45,G_44)) = k5_enumset1(A_43,B_41,C_42,D_40,E_46,F_45,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_21,B_22,C_23,F_45,E_46,G_44] : k5_enumset1(A_21,A_21,B_22,C_23,E_46,F_45,G_44) = k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k1_enumset1(E_46,F_45,G_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38])).

tff(c_50,plain,(
    ! [A_21,B_22,C_23,F_45,E_46,G_44] : k5_enumset1(A_21,A_21,B_22,C_23,E_46,F_45,G_44) = k4_enumset1(A_21,B_22,C_23,E_46,F_45,G_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.13  
% 1.59/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.14  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.59/1.14  
% 1.59/1.14  %Foreground sorts:
% 1.59/1.14  
% 1.59/1.14  
% 1.59/1.14  %Background operators:
% 1.59/1.14  
% 1.59/1.14  
% 1.59/1.14  %Foreground operators:
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.59/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.59/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.59/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.59/1.14  
% 1.59/1.14  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 1.59/1.14  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.59/1.14  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 1.59/1.14  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.59/1.14  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k1_enumset1(D_4, E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.14  tff(c_8, plain, (![A_21, B_22, C_23]: (k2_enumset1(A_21, A_21, B_22, C_23)=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.14  tff(c_38, plain, (![C_42, F_45, D_40, E_46, G_44, A_43, B_41]: (k2_xboole_0(k2_enumset1(A_43, B_41, C_42, D_40), k1_enumset1(E_46, F_45, G_44))=k5_enumset1(A_43, B_41, C_42, D_40, E_46, F_45, G_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.14  tff(c_47, plain, (![A_21, B_22, C_23, F_45, E_46, G_44]: (k5_enumset1(A_21, A_21, B_22, C_23, E_46, F_45, G_44)=k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k1_enumset1(E_46, F_45, G_44)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_38])).
% 1.59/1.14  tff(c_50, plain, (![A_21, B_22, C_23, F_45, E_46, G_44]: (k5_enumset1(A_21, A_21, B_22, C_23, E_46, F_45, G_44)=k4_enumset1(A_21, B_22, C_23, E_46, F_45, G_44))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47])).
% 1.59/1.14  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.59/1.14  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 1.59/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.14  
% 1.59/1.14  Inference rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Ref     : 0
% 1.59/1.14  #Sup     : 9
% 1.59/1.14  #Fact    : 0
% 1.59/1.14  #Define  : 0
% 1.59/1.14  #Split   : 0
% 1.59/1.14  #Chain   : 0
% 1.59/1.14  #Close   : 0
% 1.59/1.14  
% 1.59/1.14  Ordering : KBO
% 1.59/1.14  
% 1.59/1.14  Simplification rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Subsume      : 0
% 1.59/1.14  #Demod        : 2
% 1.59/1.14  #Tautology    : 8
% 1.59/1.14  #SimpNegUnit  : 0
% 1.59/1.14  #BackRed      : 1
% 1.59/1.14  
% 1.59/1.14  #Partial instantiations: 0
% 1.59/1.14  #Strategies tried      : 1
% 1.59/1.14  
% 1.59/1.14  Timing (in seconds)
% 1.59/1.14  ----------------------
% 1.59/1.15  Preprocessing        : 0.27
% 1.59/1.15  Parsing              : 0.14
% 1.59/1.15  CNF conversion       : 0.02
% 1.59/1.15  Main loop            : 0.07
% 1.59/1.15  Inferencing          : 0.04
% 1.59/1.15  Reduction            : 0.02
% 1.59/1.15  Demodulation         : 0.02
% 1.59/1.15  BG Simplification    : 0.01
% 1.59/1.15  Subsumption          : 0.01
% 1.59/1.15  Abstraction          : 0.01
% 1.59/1.15  MUC search           : 0.00
% 1.59/1.15  Cooper               : 0.00
% 1.59/1.15  Total                : 0.37
% 1.59/1.15  Index Insertion      : 0.00
% 1.59/1.15  Index Deletion       : 0.00
% 1.59/1.15  Index Matching       : 0.00
% 1.59/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
