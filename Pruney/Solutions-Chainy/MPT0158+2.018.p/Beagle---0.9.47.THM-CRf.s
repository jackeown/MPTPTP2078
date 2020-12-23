%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
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
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k2_tarski(A_1,B_2),k2_enumset1(C_3,D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [G_39,F_40,B_36,C_37,E_41,A_38,D_35] : k2_xboole_0(k1_enumset1(A_38,B_36,C_37),k2_enumset1(D_35,E_41,F_40,G_39)) = k5_enumset1(A_38,B_36,C_37,D_35,E_41,F_40,G_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [G_39,F_40,E_41,D_35,A_14,B_15] : k5_enumset1(A_14,A_14,B_15,D_35,E_41,F_40,G_39) = k2_xboole_0(k2_tarski(A_14,B_15),k2_enumset1(D_35,E_41,F_40,G_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_76,plain,(
    ! [G_39,F_40,E_41,D_35,A_14,B_15] : k5_enumset1(A_14,A_14,B_15,D_35,E_41,F_40,G_39) = k4_enumset1(A_14,B_15,D_35,E_41,F_40,G_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:59:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.14  
% 1.76/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.76/1.15  
% 1.76/1.15  %Foreground sorts:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Background operators:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Foreground operators:
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.76/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.76/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.76/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.15  
% 1.76/1.15  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 1.76/1.15  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.76/1.15  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 1.76/1.15  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.76/1.15  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_enumset1(C_3, D_4, E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.15  tff(c_6, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.76/1.15  tff(c_61, plain, (![G_39, F_40, B_36, C_37, E_41, A_38, D_35]: (k2_xboole_0(k1_enumset1(A_38, B_36, C_37), k2_enumset1(D_35, E_41, F_40, G_39))=k5_enumset1(A_38, B_36, C_37, D_35, E_41, F_40, G_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.15  tff(c_73, plain, (![G_39, F_40, E_41, D_35, A_14, B_15]: (k5_enumset1(A_14, A_14, B_15, D_35, E_41, F_40, G_39)=k2_xboole_0(k2_tarski(A_14, B_15), k2_enumset1(D_35, E_41, F_40, G_39)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 1.76/1.15  tff(c_76, plain, (![G_39, F_40, E_41, D_35, A_14, B_15]: (k5_enumset1(A_14, A_14, B_15, D_35, E_41, F_40, G_39)=k4_enumset1(A_14, B_15, D_35, E_41, F_40, G_39))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_73])).
% 1.76/1.15  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.15  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_10])).
% 1.76/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  Inference rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Ref     : 0
% 1.76/1.15  #Sup     : 22
% 1.76/1.15  #Fact    : 0
% 1.76/1.15  #Define  : 0
% 1.76/1.15  #Split   : 0
% 1.76/1.15  #Chain   : 0
% 1.76/1.15  #Close   : 0
% 1.76/1.15  
% 1.76/1.15  Ordering : KBO
% 1.76/1.15  
% 1.76/1.15  Simplification rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Subsume      : 0
% 1.76/1.15  #Demod        : 4
% 1.76/1.15  #Tautology    : 18
% 1.76/1.15  #SimpNegUnit  : 0
% 1.76/1.15  #BackRed      : 1
% 1.76/1.15  
% 1.76/1.15  #Partial instantiations: 0
% 1.76/1.15  #Strategies tried      : 1
% 1.76/1.15  
% 1.76/1.15  Timing (in seconds)
% 1.76/1.15  ----------------------
% 1.76/1.16  Preprocessing        : 0.27
% 1.76/1.16  Parsing              : 0.15
% 1.76/1.16  CNF conversion       : 0.02
% 1.76/1.16  Main loop            : 0.11
% 1.76/1.16  Inferencing          : 0.05
% 1.76/1.16  Reduction            : 0.03
% 1.76/1.16  Demodulation         : 0.03
% 1.76/1.16  BG Simplification    : 0.01
% 1.76/1.16  Subsumption          : 0.01
% 1.76/1.16  Abstraction          : 0.01
% 1.76/1.16  MUC search           : 0.00
% 1.76/1.16  Cooper               : 0.00
% 1.76/1.16  Total                : 0.40
% 1.76/1.16  Index Insertion      : 0.00
% 1.76/1.16  Index Deletion       : 0.00
% 1.76/1.16  Index Matching       : 0.00
% 1.76/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
