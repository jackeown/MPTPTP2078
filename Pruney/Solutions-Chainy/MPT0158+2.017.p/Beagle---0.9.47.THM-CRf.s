%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.79s
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
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k2_tarski(A_1,B_2),k2_enumset1(C_3,D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_47,F_42,E_41,B_46,G_44,C_45,D_43] : k2_xboole_0(k1_enumset1(A_47,B_46,C_45),k2_enumset1(D_43,E_41,F_42,G_44)) = k5_enumset1(A_47,B_46,C_45,D_43,E_41,F_42,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_21,B_22,F_42,E_41,G_44,D_43] : k5_enumset1(A_21,A_21,B_22,D_43,E_41,F_42,G_44) = k2_xboole_0(k2_tarski(A_21,B_22),k2_enumset1(D_43,E_41,F_42,G_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_40])).

tff(c_52,plain,(
    ! [A_21,B_22,F_42,E_41,G_44,D_43] : k5_enumset1(A_21,A_21,B_22,D_43,E_41,F_42,G_44) = k4_enumset1(A_21,B_22,D_43,E_41,F_42,G_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.11  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.79/1.11  
% 1.79/1.11  %Foreground sorts:
% 1.79/1.11  
% 1.79/1.11  
% 1.79/1.11  %Background operators:
% 1.79/1.11  
% 1.79/1.11  
% 1.79/1.11  %Foreground operators:
% 1.79/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.11  tff('#skF_6', type, '#skF_6': $i).
% 1.79/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.11  
% 1.79/1.12  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 1.79/1.12  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.79/1.12  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 1.79/1.12  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.79/1.12  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_enumset1(C_3, D_4, E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.12  tff(c_8, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.12  tff(c_40, plain, (![A_47, F_42, E_41, B_46, G_44, C_45, D_43]: (k2_xboole_0(k1_enumset1(A_47, B_46, C_45), k2_enumset1(D_43, E_41, F_42, G_44))=k5_enumset1(A_47, B_46, C_45, D_43, E_41, F_42, G_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.12  tff(c_49, plain, (![A_21, B_22, F_42, E_41, G_44, D_43]: (k5_enumset1(A_21, A_21, B_22, D_43, E_41, F_42, G_44)=k2_xboole_0(k2_tarski(A_21, B_22), k2_enumset1(D_43, E_41, F_42, G_44)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_40])).
% 1.79/1.12  tff(c_52, plain, (![A_21, B_22, F_42, E_41, G_44, D_43]: (k5_enumset1(A_21, A_21, B_22, D_43, E_41, F_42, G_44)=k4_enumset1(A_21, B_22, D_43, E_41, F_42, G_44))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_49])).
% 1.79/1.12  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.12  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_12])).
% 1.79/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.12  
% 1.79/1.12  Inference rules
% 1.79/1.12  ----------------------
% 1.79/1.12  #Ref     : 0
% 1.79/1.12  #Sup     : 11
% 1.79/1.12  #Fact    : 0
% 1.79/1.12  #Define  : 0
% 1.79/1.12  #Split   : 0
% 1.79/1.12  #Chain   : 0
% 1.79/1.12  #Close   : 0
% 1.79/1.12  
% 1.79/1.12  Ordering : KBO
% 1.79/1.12  
% 1.79/1.12  Simplification rules
% 1.79/1.12  ----------------------
% 1.79/1.12  #Subsume      : 0
% 1.79/1.12  #Demod        : 2
% 1.79/1.12  #Tautology    : 10
% 1.79/1.12  #SimpNegUnit  : 0
% 1.79/1.12  #BackRed      : 1
% 1.79/1.12  
% 1.79/1.12  #Partial instantiations: 0
% 1.79/1.12  #Strategies tried      : 1
% 1.79/1.12  
% 1.79/1.12  Timing (in seconds)
% 1.79/1.12  ----------------------
% 1.79/1.13  Preprocessing        : 0.28
% 1.79/1.13  Parsing              : 0.15
% 1.79/1.13  CNF conversion       : 0.02
% 1.79/1.13  Main loop            : 0.08
% 1.79/1.13  Inferencing          : 0.04
% 1.79/1.13  Reduction            : 0.02
% 1.79/1.13  Demodulation         : 0.02
% 1.79/1.13  BG Simplification    : 0.01
% 1.79/1.13  Subsumption          : 0.01
% 1.79/1.13  Abstraction          : 0.01
% 1.79/1.13  MUC search           : 0.00
% 1.79/1.13  Cooper               : 0.00
% 1.79/1.13  Total                : 0.39
% 1.79/1.13  Index Insertion      : 0.00
% 1.79/1.13  Index Deletion       : 0.00
% 1.79/1.13  Index Matching       : 0.00
% 1.79/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
