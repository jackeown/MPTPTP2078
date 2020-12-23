%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:51 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_6,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_35,B_33,C_34,D_32,E_31] : k2_xboole_0(k2_enumset1(A_35,B_33,C_34,D_32),k1_tarski(E_31)) = k3_enumset1(A_35,B_33,C_34,D_32,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_9,B_10,C_11,E_31] : k3_enumset1(A_9,A_9,B_10,C_11,E_31) = k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_tarski(E_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_94,plain,(
    ! [A_36,B_37,C_38,E_39] : k2_xboole_0(k1_enumset1(A_36,B_37,C_38),k1_tarski(E_39)) = k2_enumset1(A_36,B_37,C_38,E_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_103,plain,(
    ! [A_7,B_8,E_39] : k2_xboole_0(k2_tarski(A_7,B_8),k1_tarski(E_39)) = k2_enumset1(A_7,A_7,B_8,E_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_107,plain,(
    ! [A_40,B_41,E_42] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(E_42)) = k1_enumset1(A_40,B_41,E_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_116,plain,(
    ! [A_6,E_42] : k2_xboole_0(k1_tarski(A_6),k1_tarski(E_42)) = k1_enumset1(A_6,A_6,E_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_107])).

tff(c_119,plain,(
    ! [A_6,E_42] : k2_xboole_0(k1_tarski(A_6),k1_tarski(E_42)) = k2_tarski(A_6,E_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_12,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:02:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.13  
% 1.66/1.14  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.66/1.14  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.66/1.14  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.66/1.14  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.66/1.14  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.66/1.14  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.66/1.14  tff(f_40, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.66/1.14  tff(c_6, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.14  tff(c_4, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.14  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.14  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.14  tff(c_81, plain, (![A_35, B_33, C_34, D_32, E_31]: (k2_xboole_0(k2_enumset1(A_35, B_33, C_34, D_32), k1_tarski(E_31))=k3_enumset1(A_35, B_33, C_34, D_32, E_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.14  tff(c_90, plain, (![A_9, B_10, C_11, E_31]: (k3_enumset1(A_9, A_9, B_10, C_11, E_31)=k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_tarski(E_31)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_81])).
% 1.66/1.14  tff(c_94, plain, (![A_36, B_37, C_38, E_39]: (k2_xboole_0(k1_enumset1(A_36, B_37, C_38), k1_tarski(E_39))=k2_enumset1(A_36, B_37, C_38, E_39))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 1.66/1.14  tff(c_103, plain, (![A_7, B_8, E_39]: (k2_xboole_0(k2_tarski(A_7, B_8), k1_tarski(E_39))=k2_enumset1(A_7, A_7, B_8, E_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_94])).
% 1.66/1.14  tff(c_107, plain, (![A_40, B_41, E_42]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(E_42))=k1_enumset1(A_40, B_41, E_42))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_103])).
% 1.66/1.14  tff(c_116, plain, (![A_6, E_42]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(E_42))=k1_enumset1(A_6, A_6, E_42))), inference(superposition, [status(thm), theory('equality')], [c_4, c_107])).
% 1.66/1.14  tff(c_119, plain, (![A_6, E_42]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(E_42))=k2_tarski(A_6, E_42))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_116])).
% 1.66/1.14  tff(c_12, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.14  tff(c_14, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.66/1.14  tff(c_15, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 1.66/1.14  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_15])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 24
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 0
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 0
% 1.66/1.14  #Demod        : 5
% 1.66/1.14  #Tautology    : 20
% 1.66/1.14  #SimpNegUnit  : 0
% 1.66/1.14  #BackRed      : 1
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.15  Preprocessing        : 0.27
% 1.66/1.15  Parsing              : 0.14
% 1.66/1.15  CNF conversion       : 0.01
% 1.66/1.15  Main loop            : 0.10
% 1.66/1.15  Inferencing          : 0.05
% 1.66/1.15  Reduction            : 0.03
% 1.66/1.15  Demodulation         : 0.03
% 1.66/1.15  BG Simplification    : 0.01
% 1.66/1.15  Subsumption          : 0.01
% 1.66/1.15  Abstraction          : 0.01
% 1.66/1.15  MUC search           : 0.00
% 1.66/1.15  Cooper               : 0.00
% 1.66/1.15  Total                : 0.40
% 1.66/1.15  Index Insertion      : 0.00
% 1.66/1.15  Index Deletion       : 0.00
% 1.66/1.15  Index Matching       : 0.00
% 1.66/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
