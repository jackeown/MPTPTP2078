%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:24 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(c_4,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k1_tarski(A_7),k1_enumset1(B_8,C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_26] : k1_enumset1(A_26,A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [E_48,C_51,D_49,B_50,A_52,F_47] : k2_xboole_0(k1_enumset1(A_52,B_50,C_51),k1_enumset1(D_49,E_48,F_47)) = k4_enumset1(A_52,B_50,C_51,D_49,E_48,F_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_26,D_49,E_48,F_47] : k4_enumset1(A_26,A_26,A_26,D_49,E_48,F_47) = k2_xboole_0(k1_tarski(A_26),k1_enumset1(D_49,E_48,F_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_148])).

tff(c_163,plain,(
    ! [A_26,D_49,E_48,F_47] : k4_enumset1(A_26,A_26,A_26,D_49,E_48,F_47) = k2_enumset1(A_26,D_49,E_48,F_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_157])).

tff(c_14,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:22:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.79/1.14  
% 1.79/1.14  %Foreground sorts:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Background operators:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Foreground operators:
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.14  
% 1.79/1.15  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.79/1.15  tff(f_37, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 1.79/1.15  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 1.79/1.15  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 1.79/1.15  tff(c_4, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k1_tarski(A_7), k1_enumset1(B_8, C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.15  tff(c_12, plain, (![A_26]: (k1_enumset1(A_26, A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.15  tff(c_148, plain, (![E_48, C_51, D_49, B_50, A_52, F_47]: (k2_xboole_0(k1_enumset1(A_52, B_50, C_51), k1_enumset1(D_49, E_48, F_47))=k4_enumset1(A_52, B_50, C_51, D_49, E_48, F_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.15  tff(c_157, plain, (![A_26, D_49, E_48, F_47]: (k4_enumset1(A_26, A_26, A_26, D_49, E_48, F_47)=k2_xboole_0(k1_tarski(A_26), k1_enumset1(D_49, E_48, F_47)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_148])).
% 1.79/1.15  tff(c_163, plain, (![A_26, D_49, E_48, F_47]: (k4_enumset1(A_26, A_26, A_26, D_49, E_48, F_47)=k2_enumset1(A_26, D_49, E_48, F_47))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_157])).
% 1.79/1.15  tff(c_14, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.15  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_14])).
% 1.79/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  Inference rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Ref     : 0
% 1.79/1.15  #Sup     : 38
% 1.79/1.15  #Fact    : 0
% 1.79/1.15  #Define  : 0
% 1.79/1.15  #Split   : 0
% 1.79/1.15  #Chain   : 0
% 1.79/1.15  #Close   : 0
% 1.79/1.15  
% 1.79/1.15  Ordering : KBO
% 1.79/1.15  
% 1.79/1.15  Simplification rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Subsume      : 5
% 1.79/1.15  #Demod        : 3
% 1.79/1.15  #Tautology    : 24
% 1.79/1.15  #SimpNegUnit  : 0
% 1.79/1.15  #BackRed      : 1
% 1.79/1.15  
% 1.79/1.15  #Partial instantiations: 0
% 1.79/1.15  #Strategies tried      : 1
% 1.79/1.15  
% 1.79/1.15  Timing (in seconds)
% 1.79/1.15  ----------------------
% 1.79/1.16  Preprocessing        : 0.28
% 1.79/1.16  Parsing              : 0.15
% 1.79/1.16  CNF conversion       : 0.02
% 1.79/1.16  Main loop            : 0.13
% 1.79/1.16  Inferencing          : 0.06
% 1.79/1.16  Reduction            : 0.04
% 1.79/1.16  Demodulation         : 0.04
% 1.79/1.16  BG Simplification    : 0.01
% 1.79/1.16  Subsumption          : 0.01
% 1.79/1.16  Abstraction          : 0.01
% 1.79/1.16  MUC search           : 0.00
% 1.79/1.16  Cooper               : 0.00
% 1.79/1.16  Total                : 0.43
% 1.79/1.16  Index Insertion      : 0.00
% 1.79/1.16  Index Deletion       : 0.00
% 1.79/1.16  Index Matching       : 0.00
% 1.79/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
