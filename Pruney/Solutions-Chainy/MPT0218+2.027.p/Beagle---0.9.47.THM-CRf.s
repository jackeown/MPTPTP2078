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
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_6,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_xboole_0(k1_enumset1(A_21,B_22,C_23),k1_tarski(D_24)) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [A_25,B_26,C_27,D_28] : r1_tarski(k1_enumset1(A_25,B_26,C_27),k2_enumset1(A_25,B_26,C_27,D_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_60,plain,(
    ! [A_10,B_11,C_12] : r1_tarski(k1_enumset1(A_10,A_10,B_11),k1_enumset1(A_10,B_11,C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_66,plain,(
    ! [A_29,B_30,C_31] : r1_tarski(k2_tarski(A_29,B_30),k1_enumset1(A_29,B_30,C_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_69,plain,(
    ! [A_8,B_9] : r1_tarski(k2_tarski(A_8,A_8),k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_73,plain,(
    ! [A_8,B_9] : r1_tarski(k1_tarski(A_8),k2_tarski(A_8,B_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_12,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.14  
% 1.70/1.15  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.70/1.15  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.70/1.15  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.70/1.15  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.70/1.15  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.70/1.15  tff(f_38, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.70/1.15  tff(c_6, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.15  tff(c_8, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.15  tff(c_10, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.15  tff(c_41, plain, (![A_21, B_22, C_23, D_24]: (k2_xboole_0(k1_enumset1(A_21, B_22, C_23), k1_tarski(D_24))=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.15  tff(c_57, plain, (![A_25, B_26, C_27, D_28]: (r1_tarski(k1_enumset1(A_25, B_26, C_27), k2_enumset1(A_25, B_26, C_27, D_28)))), inference(superposition, [status(thm), theory('equality')], [c_41, c_2])).
% 1.70/1.15  tff(c_60, plain, (![A_10, B_11, C_12]: (r1_tarski(k1_enumset1(A_10, A_10, B_11), k1_enumset1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 1.70/1.15  tff(c_66, plain, (![A_29, B_30, C_31]: (r1_tarski(k2_tarski(A_29, B_30), k1_enumset1(A_29, B_30, C_31)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_60])).
% 1.70/1.15  tff(c_69, plain, (![A_8, B_9]: (r1_tarski(k2_tarski(A_8, A_8), k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 1.70/1.15  tff(c_73, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), k2_tarski(A_8, B_9)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 1.70/1.15  tff(c_12, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.15  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_12])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 14
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 6
% 1.70/1.15  #Tautology    : 8
% 1.70/1.15  #SimpNegUnit  : 0
% 1.70/1.15  #BackRed      : 1
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.15  Preprocessing        : 0.27
% 1.70/1.15  Parsing              : 0.15
% 1.70/1.15  CNF conversion       : 0.01
% 1.70/1.15  Main loop            : 0.08
% 1.70/1.15  Inferencing          : 0.04
% 1.70/1.15  Reduction            : 0.03
% 1.70/1.15  Demodulation         : 0.02
% 1.70/1.15  BG Simplification    : 0.01
% 1.70/1.15  Subsumption          : 0.01
% 1.70/1.15  Abstraction          : 0.01
% 1.70/1.15  MUC search           : 0.00
% 1.70/1.15  Cooper               : 0.00
% 1.70/1.15  Total                : 0.37
% 1.70/1.15  Index Insertion      : 0.00
% 1.70/1.15  Index Deletion       : 0.00
% 1.70/1.15  Index Matching       : 0.00
% 1.70/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
