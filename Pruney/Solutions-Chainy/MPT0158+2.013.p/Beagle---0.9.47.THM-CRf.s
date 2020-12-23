%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
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
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k1_tarski(A_1),k3_enumset1(B_2,C_3,D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ! [E_44,F_41,G_46,B_43,C_47,A_45,D_42] : k2_xboole_0(k2_tarski(A_45,B_43),k3_enumset1(C_47,D_42,E_44,F_41,G_46)) = k5_enumset1(A_45,B_43,C_47,D_42,E_44,F_41,G_46) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [E_44,F_41,G_46,C_47,D_42,A_27] : k5_enumset1(A_27,A_27,C_47,D_42,E_44,F_41,G_46) = k2_xboole_0(k1_tarski(A_27),k3_enumset1(C_47,D_42,E_44,F_41,G_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_52,plain,(
    ! [E_44,F_41,G_46,C_47,D_42,A_27] : k5_enumset1(A_27,A_27,C_47,D_42,E_44,F_41,G_46) = k4_enumset1(A_27,C_47,D_42,E_44,F_41,G_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.34  % CPULimit   : 60
% 0.18/0.34  % DateTime   : Tue Dec  1 18:31:34 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.67/1.09  
% 1.67/1.09  %Foreground sorts:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Background operators:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Foreground operators:
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.09  tff('#skF_5', type, '#skF_5': $i).
% 1.67/1.09  tff('#skF_6', type, '#skF_6': $i).
% 1.67/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.09  
% 1.67/1.10  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 1.67/1.10  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.67/1.10  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 1.67/1.10  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.67/1.10  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k1_tarski(A_1), k3_enumset1(B_2, C_3, D_4, E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.10  tff(c_10, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.10  tff(c_40, plain, (![E_44, F_41, G_46, B_43, C_47, A_45, D_42]: (k2_xboole_0(k2_tarski(A_45, B_43), k3_enumset1(C_47, D_42, E_44, F_41, G_46))=k5_enumset1(A_45, B_43, C_47, D_42, E_44, F_41, G_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.10  tff(c_49, plain, (![E_44, F_41, G_46, C_47, D_42, A_27]: (k5_enumset1(A_27, A_27, C_47, D_42, E_44, F_41, G_46)=k2_xboole_0(k1_tarski(A_27), k3_enumset1(C_47, D_42, E_44, F_41, G_46)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_40])).
% 1.67/1.10  tff(c_52, plain, (![E_44, F_41, G_46, C_47, D_42, A_27]: (k5_enumset1(A_27, A_27, C_47, D_42, E_44, F_41, G_46)=k4_enumset1(A_27, C_47, D_42, E_44, F_41, G_46))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_49])).
% 1.67/1.10  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.10  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_12])).
% 1.67/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  Inference rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Ref     : 0
% 1.67/1.10  #Sup     : 11
% 1.67/1.10  #Fact    : 0
% 1.67/1.10  #Define  : 0
% 1.67/1.10  #Split   : 0
% 1.67/1.10  #Chain   : 0
% 1.67/1.10  #Close   : 0
% 1.67/1.10  
% 1.67/1.10  Ordering : KBO
% 1.67/1.10  
% 1.67/1.10  Simplification rules
% 1.67/1.10  ----------------------
% 1.67/1.10  #Subsume      : 0
% 1.67/1.10  #Demod        : 2
% 1.67/1.10  #Tautology    : 10
% 1.67/1.10  #SimpNegUnit  : 0
% 1.67/1.10  #BackRed      : 1
% 1.67/1.10  
% 1.67/1.10  #Partial instantiations: 0
% 1.67/1.10  #Strategies tried      : 1
% 1.67/1.10  
% 1.67/1.10  Timing (in seconds)
% 1.67/1.10  ----------------------
% 1.67/1.10  Preprocessing        : 0.27
% 1.67/1.10  Parsing              : 0.14
% 1.67/1.10  CNF conversion       : 0.02
% 1.67/1.10  Main loop            : 0.08
% 1.67/1.10  Inferencing          : 0.04
% 1.67/1.10  Reduction            : 0.02
% 1.67/1.10  Demodulation         : 0.02
% 1.67/1.10  BG Simplification    : 0.01
% 1.67/1.10  Subsumption          : 0.01
% 1.67/1.10  Abstraction          : 0.01
% 1.67/1.10  MUC search           : 0.00
% 1.67/1.10  Cooper               : 0.00
% 1.67/1.10  Total                : 0.37
% 1.67/1.10  Index Insertion      : 0.00
% 1.67/1.10  Index Deletion       : 0.00
% 1.67/1.10  Index Matching       : 0.00
% 1.67/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
