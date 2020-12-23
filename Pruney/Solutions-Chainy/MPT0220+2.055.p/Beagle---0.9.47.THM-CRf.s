%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:11 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_8,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k3_enumset1(A_14,A_14,B_15,C_16,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [C_33,D_31,E_30,B_34,A_32] : k2_xboole_0(k1_enumset1(A_32,B_34,C_33),k2_tarski(D_31,E_30)) = k3_enumset1(A_32,B_34,C_33,D_31,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_9,B_10,D_31,E_30] : k3_enumset1(A_9,A_9,B_10,D_31,E_30) = k2_xboole_0(k2_tarski(A_9,B_10),k2_tarski(D_31,E_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_76,plain,(
    ! [A_35,B_36,D_37,E_38] : k2_xboole_0(k2_tarski(A_35,B_36),k2_tarski(D_37,E_38)) = k2_enumset1(A_35,B_36,D_37,E_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_85,plain,(
    ! [A_8,D_37,E_38] : k2_xboole_0(k1_tarski(A_8),k2_tarski(D_37,E_38)) = k2_enumset1(A_8,A_8,D_37,E_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_91,plain,(
    ! [A_8,D_37,E_38] : k2_xboole_0(k1_tarski(A_8),k2_tarski(D_37,E_38)) = k1_enumset1(A_8,D_37,E_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.09  
% 1.71/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.09  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.71/1.09  
% 1.71/1.09  %Foreground sorts:
% 1.71/1.09  
% 1.71/1.09  
% 1.71/1.09  %Background operators:
% 1.71/1.09  
% 1.71/1.09  
% 1.71/1.09  %Foreground operators:
% 1.71/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.09  
% 1.71/1.10  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.71/1.10  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.71/1.10  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.71/1.10  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.71/1.10  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 1.71/1.10  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.71/1.10  tff(c_8, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.10  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.10  tff(c_6, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.10  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k3_enumset1(A_14, A_14, B_15, C_16, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.10  tff(c_60, plain, (![C_33, D_31, E_30, B_34, A_32]: (k2_xboole_0(k1_enumset1(A_32, B_34, C_33), k2_tarski(D_31, E_30))=k3_enumset1(A_32, B_34, C_33, D_31, E_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.10  tff(c_69, plain, (![A_9, B_10, D_31, E_30]: (k3_enumset1(A_9, A_9, B_10, D_31, E_30)=k2_xboole_0(k2_tarski(A_9, B_10), k2_tarski(D_31, E_30)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_60])).
% 1.71/1.10  tff(c_76, plain, (![A_35, B_36, D_37, E_38]: (k2_xboole_0(k2_tarski(A_35, B_36), k2_tarski(D_37, E_38))=k2_enumset1(A_35, B_36, D_37, E_38))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_69])).
% 1.71/1.10  tff(c_85, plain, (![A_8, D_37, E_38]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(D_37, E_38))=k2_enumset1(A_8, A_8, D_37, E_38))), inference(superposition, [status(thm), theory('equality')], [c_6, c_76])).
% 1.71/1.10  tff(c_91, plain, (![A_8, D_37, E_38]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(D_37, E_38))=k1_enumset1(A_8, D_37, E_38))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_85])).
% 1.71/1.10  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.10  tff(c_92, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_14])).
% 1.71/1.10  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_92])).
% 1.71/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  Inference rules
% 1.71/1.10  ----------------------
% 1.71/1.10  #Ref     : 0
% 1.71/1.10  #Sup     : 18
% 1.71/1.10  #Fact    : 0
% 1.71/1.10  #Define  : 0
% 1.71/1.10  #Split   : 0
% 1.71/1.10  #Chain   : 0
% 1.71/1.10  #Close   : 0
% 1.71/1.10  
% 1.71/1.10  Ordering : KBO
% 1.71/1.10  
% 1.71/1.10  Simplification rules
% 1.71/1.10  ----------------------
% 1.71/1.10  #Subsume      : 0
% 1.71/1.10  #Demod        : 4
% 1.71/1.10  #Tautology    : 14
% 1.71/1.10  #SimpNegUnit  : 0
% 1.71/1.10  #BackRed      : 1
% 1.71/1.10  
% 1.71/1.10  #Partial instantiations: 0
% 1.71/1.10  #Strategies tried      : 1
% 1.71/1.10  
% 1.71/1.10  Timing (in seconds)
% 1.71/1.10  ----------------------
% 1.71/1.10  Preprocessing        : 0.26
% 1.71/1.10  Parsing              : 0.14
% 1.71/1.10  CNF conversion       : 0.01
% 1.71/1.10  Main loop            : 0.09
% 1.71/1.10  Inferencing          : 0.04
% 1.71/1.10  Reduction            : 0.03
% 1.71/1.10  Demodulation         : 0.02
% 1.71/1.10  BG Simplification    : 0.01
% 1.71/1.10  Subsumption          : 0.01
% 1.71/1.10  Abstraction          : 0.01
% 1.71/1.10  MUC search           : 0.00
% 1.71/1.10  Cooper               : 0.00
% 1.71/1.10  Total                : 0.37
% 1.71/1.10  Index Insertion      : 0.00
% 1.71/1.10  Index Deletion       : 0.00
% 1.71/1.10  Index Matching       : 0.00
% 1.71/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
