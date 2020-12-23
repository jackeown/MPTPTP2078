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
% DateTime   : Thu Dec  3 09:46:20 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] : k2_xboole_0(k1_tarski(A_5),k3_enumset1(B_6,C_7,D_8,E_9,F_10)) = k4_enumset1(A_5,B_6,C_7,D_8,E_9,F_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [D_52,F_53,A_56,E_57,C_55,B_54] : k2_xboole_0(k1_tarski(A_56),k3_enumset1(B_54,C_55,D_52,E_57,F_53)) = k4_enumset1(A_56,B_54,C_55,D_52,E_57,F_53) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [D_52,F_53,A_56,E_57,C_55,B_54] : k2_xboole_0(k1_tarski(A_56),k4_enumset1(A_56,B_54,C_55,D_52,E_57,F_53)) = k2_xboole_0(k1_tarski(A_56),k3_enumset1(B_54,C_55,D_52,E_57,F_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_485,plain,(
    ! [C_103,B_108,E_105,F_104,A_107,D_106] : k2_xboole_0(k1_tarski(A_107),k4_enumset1(A_107,B_108,C_103,D_106,E_105,F_104)) = k4_enumset1(A_107,B_108,C_103,D_106,E_105,F_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_8,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k1_tarski(A_11),k4_enumset1(B_12,C_13,D_14,E_15,F_16,G_17)) = k5_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_491,plain,(
    ! [C_103,B_108,E_105,F_104,A_107,D_106] : k5_enumset1(A_107,A_107,B_108,C_103,D_106,E_105,F_104) = k4_enumset1(A_107,B_108,C_103,D_106,E_105,F_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_8])).

tff(c_20,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:27:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.52  
% 3.10/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.52  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.10/1.52  
% 3.10/1.52  %Foreground sorts:
% 3.10/1.52  
% 3.10/1.52  
% 3.10/1.52  %Background operators:
% 3.10/1.52  
% 3.10/1.52  
% 3.10/1.52  %Foreground operators:
% 3.10/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.52  
% 3.10/1.53  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.10/1.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 3.10/1.53  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 3.10/1.53  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.10/1.53  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (k2_xboole_0(k1_tarski(A_5), k3_enumset1(B_6, C_7, D_8, E_9, F_10))=k4_enumset1(A_5, B_6, C_7, D_8, E_9, F_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.53  tff(c_92, plain, (![D_52, F_53, A_56, E_57, C_55, B_54]: (k2_xboole_0(k1_tarski(A_56), k3_enumset1(B_54, C_55, D_52, E_57, F_53))=k4_enumset1(A_56, B_54, C_55, D_52, E_57, F_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.53  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.53  tff(c_98, plain, (![D_52, F_53, A_56, E_57, C_55, B_54]: (k2_xboole_0(k1_tarski(A_56), k4_enumset1(A_56, B_54, C_55, D_52, E_57, F_53))=k2_xboole_0(k1_tarski(A_56), k3_enumset1(B_54, C_55, D_52, E_57, F_53)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 3.10/1.53  tff(c_485, plain, (![C_103, B_108, E_105, F_104, A_107, D_106]: (k2_xboole_0(k1_tarski(A_107), k4_enumset1(A_107, B_108, C_103, D_106, E_105, F_104))=k4_enumset1(A_107, B_108, C_103, D_106, E_105, F_104))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_98])).
% 3.10/1.53  tff(c_8, plain, (![G_17, F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k1_tarski(A_11), k4_enumset1(B_12, C_13, D_14, E_15, F_16, G_17))=k5_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.53  tff(c_491, plain, (![C_103, B_108, E_105, F_104, A_107, D_106]: (k5_enumset1(A_107, A_107, B_108, C_103, D_106, E_105, F_104)=k4_enumset1(A_107, B_108, C_103, D_106, E_105, F_104))), inference(superposition, [status(thm), theory('equality')], [c_485, c_8])).
% 3.10/1.53  tff(c_20, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.10/1.53  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_491, c_20])).
% 3.10/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.53  
% 3.10/1.53  Inference rules
% 3.10/1.53  ----------------------
% 3.10/1.53  #Ref     : 0
% 3.10/1.53  #Sup     : 297
% 3.10/1.53  #Fact    : 0
% 3.10/1.53  #Define  : 0
% 3.10/1.53  #Split   : 0
% 3.10/1.53  #Chain   : 0
% 3.10/1.53  #Close   : 0
% 3.10/1.53  
% 3.10/1.53  Ordering : KBO
% 3.10/1.53  
% 3.10/1.53  Simplification rules
% 3.10/1.53  ----------------------
% 3.10/1.53  #Subsume      : 11
% 3.10/1.53  #Demod        : 276
% 3.10/1.53  #Tautology    : 233
% 3.10/1.53  #SimpNegUnit  : 0
% 3.10/1.53  #BackRed      : 1
% 3.10/1.53  
% 3.10/1.53  #Partial instantiations: 0
% 3.10/1.53  #Strategies tried      : 1
% 3.10/1.53  
% 3.10/1.53  Timing (in seconds)
% 3.10/1.53  ----------------------
% 3.10/1.54  Preprocessing        : 0.32
% 3.10/1.54  Parsing              : 0.16
% 3.10/1.54  CNF conversion       : 0.02
% 3.10/1.54  Main loop            : 0.40
% 3.10/1.54  Inferencing          : 0.17
% 3.10/1.54  Reduction            : 0.16
% 3.10/1.54  Demodulation         : 0.13
% 3.10/1.54  BG Simplification    : 0.02
% 3.10/1.54  Subsumption          : 0.04
% 3.10/1.54  Abstraction          : 0.03
% 3.10/1.54  MUC search           : 0.00
% 3.10/1.54  Cooper               : 0.00
% 3.10/1.54  Total                : 0.74
% 3.22/1.54  Index Insertion      : 0.00
% 3.22/1.54  Index Deletion       : 0.00
% 3.22/1.54  Index Matching       : 0.00
% 3.22/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
