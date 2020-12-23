%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:21 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k3_enumset1(A_1,B_2,C_3,D_4,E_5),k1_tarski(F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k4_enumset1(A_21,A_21,B_22,C_23,D_24,E_25) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [D_39,F_38,E_37,B_42,G_40,A_43,C_41] : k2_xboole_0(k4_enumset1(A_43,B_42,C_41,D_39,E_37,F_38),k1_tarski(G_40)) = k5_enumset1(A_43,B_42,C_41,D_39,E_37,F_38,G_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_21,B_22,D_24,C_23,E_25,G_40] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,G_40) = k2_xboole_0(k3_enumset1(A_21,B_22,C_23,D_24,E_25),k1_tarski(G_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_29])).

tff(c_41,plain,(
    ! [A_21,B_22,D_24,C_23,E_25,G_40] : k5_enumset1(A_21,A_21,B_22,C_23,D_24,E_25,G_40) = k4_enumset1(A_21,B_22,C_23,D_24,E_25,G_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.41  
% 1.87/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.41  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.41  
% 1.87/1.41  %Foreground sorts:
% 1.87/1.41  
% 1.87/1.41  
% 1.87/1.41  %Background operators:
% 1.87/1.41  
% 1.87/1.41  
% 1.87/1.41  %Foreground operators:
% 1.87/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.41  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.41  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.41  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.41  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.41  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.41  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.87/1.41  
% 1.87/1.42  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 1.87/1.42  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.87/1.42  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 1.87/1.42  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.87/1.42  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k3_enumset1(A_1, B_2, C_3, D_4, E_5), k1_tarski(F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.42  tff(c_8, plain, (![A_21, B_22, D_24, C_23, E_25]: (k4_enumset1(A_21, A_21, B_22, C_23, D_24, E_25)=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.42  tff(c_29, plain, (![D_39, F_38, E_37, B_42, G_40, A_43, C_41]: (k2_xboole_0(k4_enumset1(A_43, B_42, C_41, D_39, E_37, F_38), k1_tarski(G_40))=k5_enumset1(A_43, B_42, C_41, D_39, E_37, F_38, G_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.42  tff(c_38, plain, (![A_21, B_22, D_24, C_23, E_25, G_40]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, G_40)=k2_xboole_0(k3_enumset1(A_21, B_22, C_23, D_24, E_25), k1_tarski(G_40)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_29])).
% 1.87/1.42  tff(c_41, plain, (![A_21, B_22, D_24, C_23, E_25, G_40]: (k5_enumset1(A_21, A_21, B_22, C_23, D_24, E_25, G_40)=k4_enumset1(A_21, B_22, C_23, D_24, E_25, G_40))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 1.87/1.42  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.87/1.42  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_10])).
% 1.87/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.42  
% 1.87/1.42  Inference rules
% 1.87/1.42  ----------------------
% 1.87/1.42  #Ref     : 0
% 1.87/1.42  #Sup     : 7
% 1.87/1.42  #Fact    : 0
% 1.87/1.42  #Define  : 0
% 1.87/1.42  #Split   : 0
% 1.87/1.42  #Chain   : 0
% 1.87/1.42  #Close   : 0
% 1.87/1.42  
% 1.87/1.42  Ordering : KBO
% 1.87/1.42  
% 1.87/1.42  Simplification rules
% 1.87/1.42  ----------------------
% 1.87/1.42  #Subsume      : 0
% 1.87/1.42  #Demod        : 2
% 1.87/1.42  #Tautology    : 6
% 1.87/1.42  #SimpNegUnit  : 0
% 1.87/1.42  #BackRed      : 1
% 1.87/1.42  
% 1.87/1.42  #Partial instantiations: 0
% 1.87/1.42  #Strategies tried      : 1
% 1.87/1.42  
% 1.87/1.42  Timing (in seconds)
% 1.87/1.43  ----------------------
% 1.87/1.43  Preprocessing        : 0.43
% 1.87/1.43  Parsing              : 0.22
% 1.87/1.43  CNF conversion       : 0.03
% 1.87/1.43  Main loop            : 0.11
% 1.87/1.43  Inferencing          : 0.05
% 1.87/1.43  Reduction            : 0.03
% 1.87/1.43  Demodulation         : 0.03
% 1.87/1.43  BG Simplification    : 0.02
% 1.87/1.43  Subsumption          : 0.01
% 1.87/1.43  Abstraction          : 0.01
% 1.87/1.43  MUC search           : 0.00
% 1.87/1.43  Cooper               : 0.00
% 1.87/1.43  Total                : 0.58
% 1.87/1.43  Index Insertion      : 0.00
% 1.87/1.43  Index Deletion       : 0.00
% 1.87/1.43  Index Matching       : 0.00
% 1.87/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
