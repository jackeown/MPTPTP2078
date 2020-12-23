%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:16 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_tarski(D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [E_26,C_29,B_25,A_27,D_28] : k2_xboole_0(k2_enumset1(A_27,B_25,C_29,D_28),k1_tarski(E_26)) = k3_enumset1(A_27,B_25,C_29,D_28,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_15,B_16,C_17,E_26] : k3_enumset1(A_15,A_15,B_16,C_17,E_26) = k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k1_tarski(E_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_29])).

tff(c_41,plain,(
    ! [A_15,B_16,C_17,E_26] : k3_enumset1(A_15,A_15,B_16,C_17,E_26) = k2_enumset1(A_15,B_16,C_17,E_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_10,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.07  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.56/1.07  
% 1.56/1.07  %Foreground sorts:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Background operators:
% 1.56/1.07  
% 1.56/1.07  
% 1.56/1.07  %Foreground operators:
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.56/1.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.56/1.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.56/1.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.56/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.56/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.07  tff('#skF_4', type, '#skF_4': $i).
% 1.56/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.07  
% 1.56/1.07  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.56/1.07  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.56/1.07  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.56/1.07  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.56/1.07  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k1_tarski(D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.56/1.07  tff(c_8, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.07  tff(c_29, plain, (![E_26, C_29, B_25, A_27, D_28]: (k2_xboole_0(k2_enumset1(A_27, B_25, C_29, D_28), k1_tarski(E_26))=k3_enumset1(A_27, B_25, C_29, D_28, E_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.07  tff(c_38, plain, (![A_15, B_16, C_17, E_26]: (k3_enumset1(A_15, A_15, B_16, C_17, E_26)=k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k1_tarski(E_26)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_29])).
% 1.56/1.07  tff(c_41, plain, (![A_15, B_16, C_17, E_26]: (k3_enumset1(A_15, A_15, B_16, C_17, E_26)=k2_enumset1(A_15, B_16, C_17, E_26))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 1.56/1.07  tff(c_10, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.56/1.07  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_10])).
% 1.56/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.07  
% 1.56/1.07  Inference rules
% 1.56/1.07  ----------------------
% 1.56/1.07  #Ref     : 0
% 1.56/1.07  #Sup     : 7
% 1.56/1.07  #Fact    : 0
% 1.56/1.07  #Define  : 0
% 1.56/1.07  #Split   : 0
% 1.56/1.07  #Chain   : 0
% 1.56/1.07  #Close   : 0
% 1.56/1.07  
% 1.56/1.07  Ordering : KBO
% 1.56/1.07  
% 1.56/1.07  Simplification rules
% 1.56/1.07  ----------------------
% 1.56/1.07  #Subsume      : 0
% 1.56/1.07  #Demod        : 2
% 1.56/1.07  #Tautology    : 6
% 1.56/1.07  #SimpNegUnit  : 0
% 1.56/1.07  #BackRed      : 1
% 1.56/1.07  
% 1.56/1.07  #Partial instantiations: 0
% 1.56/1.07  #Strategies tried      : 1
% 1.56/1.07  
% 1.56/1.08  Timing (in seconds)
% 1.56/1.08  ----------------------
% 1.56/1.08  Preprocessing        : 0.27
% 1.56/1.08  Parsing              : 0.14
% 1.56/1.08  CNF conversion       : 0.01
% 1.56/1.08  Main loop            : 0.07
% 1.56/1.08  Inferencing          : 0.03
% 1.56/1.08  Reduction            : 0.02
% 1.56/1.08  Demodulation         : 0.02
% 1.56/1.08  BG Simplification    : 0.01
% 1.56/1.08  Subsumption          : 0.01
% 1.56/1.08  Abstraction          : 0.01
% 1.56/1.08  MUC search           : 0.00
% 1.56/1.08  Cooper               : 0.00
% 1.56/1.08  Total                : 0.35
% 1.56/1.08  Index Insertion      : 0.00
% 1.56/1.08  Index Deletion       : 0.00
% 1.65/1.08  Index Matching       : 0.00
% 1.65/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
