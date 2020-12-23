%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:51 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_22,B_23,C_24,D_25] : k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k1_tarski(D_25)) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_6,B_7,D_25] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(D_25)) = k2_enumset1(A_6,A_6,B_7,D_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_83,plain,(
    ! [A_26,B_27,D_28] : k2_xboole_0(k2_tarski(A_26,B_27),k1_tarski(D_28)) = k1_enumset1(A_26,B_27,D_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_92,plain,(
    ! [A_5,D_28] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_28)) = k1_enumset1(A_5,A_5,D_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_83])).

tff(c_95,plain,(
    ! [A_5,D_28] : k2_xboole_0(k1_tarski(A_5),k1_tarski(D_28)) = k2_tarski(A_5,D_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_10,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.51  
% 1.95/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.52  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.95/1.52  
% 1.95/1.52  %Foreground sorts:
% 1.95/1.52  
% 1.95/1.52  
% 1.95/1.52  %Background operators:
% 1.95/1.52  
% 1.95/1.52  
% 1.95/1.52  %Foreground operators:
% 1.95/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.52  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.52  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.52  
% 1.95/1.53  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.53  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.53  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.95/1.53  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.95/1.53  tff(f_35, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.95/1.53  tff(f_38, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.95/1.53  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.53  tff(c_4, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.53  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.53  tff(c_70, plain, (![A_22, B_23, C_24, D_25]: (k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k1_tarski(D_25))=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.53  tff(c_79, plain, (![A_6, B_7, D_25]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(D_25))=k2_enumset1(A_6, A_6, B_7, D_25))), inference(superposition, [status(thm), theory('equality')], [c_6, c_70])).
% 1.95/1.53  tff(c_83, plain, (![A_26, B_27, D_28]: (k2_xboole_0(k2_tarski(A_26, B_27), k1_tarski(D_28))=k1_enumset1(A_26, B_27, D_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_79])).
% 1.95/1.53  tff(c_92, plain, (![A_5, D_28]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_28))=k1_enumset1(A_5, A_5, D_28))), inference(superposition, [status(thm), theory('equality')], [c_4, c_83])).
% 1.95/1.53  tff(c_95, plain, (![A_5, D_28]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(D_28))=k2_tarski(A_5, D_28))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 1.95/1.53  tff(c_10, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.53  tff(c_12, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.95/1.53  tff(c_13, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.95/1.53  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_13])).
% 1.95/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.53  
% 1.95/1.53  Inference rules
% 1.95/1.53  ----------------------
% 1.95/1.53  #Ref     : 0
% 1.95/1.53  #Sup     : 19
% 1.95/1.53  #Fact    : 0
% 1.95/1.53  #Define  : 0
% 1.95/1.53  #Split   : 0
% 1.95/1.53  #Chain   : 0
% 1.95/1.53  #Close   : 0
% 1.95/1.53  
% 1.95/1.53  Ordering : KBO
% 1.95/1.53  
% 1.95/1.53  Simplification rules
% 1.95/1.53  ----------------------
% 1.95/1.53  #Subsume      : 0
% 1.95/1.53  #Demod        : 4
% 1.95/1.53  #Tautology    : 16
% 1.95/1.53  #SimpNegUnit  : 0
% 1.95/1.53  #BackRed      : 1
% 1.95/1.53  
% 1.95/1.53  #Partial instantiations: 0
% 1.95/1.53  #Strategies tried      : 1
% 1.95/1.53  
% 1.95/1.53  Timing (in seconds)
% 1.95/1.53  ----------------------
% 1.95/1.54  Preprocessing        : 0.42
% 1.95/1.54  Parsing              : 0.22
% 1.95/1.54  CNF conversion       : 0.02
% 1.95/1.54  Main loop            : 0.14
% 1.95/1.54  Inferencing          : 0.06
% 1.95/1.54  Reduction            : 0.05
% 1.95/1.54  Demodulation         : 0.04
% 1.95/1.54  BG Simplification    : 0.01
% 1.95/1.54  Subsumption          : 0.01
% 1.95/1.54  Abstraction          : 0.01
% 1.95/1.54  MUC search           : 0.00
% 1.95/1.54  Cooper               : 0.00
% 1.95/1.54  Total                : 0.61
% 1.95/1.54  Index Insertion      : 0.00
% 1.95/1.54  Index Deletion       : 0.00
% 2.06/1.54  Index Matching       : 0.00
% 2.06/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
