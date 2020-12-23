%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  48 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_24,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [B_27,A_28] : k3_tarski(k2_tarski(B_27,A_28)) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_16,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [B_27,A_28] : k2_xboole_0(B_27,A_28) = k2_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_16])).

tff(c_26,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_221,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_224,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_221])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_243,plain,(
    ! [A_35,C_36,B_37] :
      ( r2_hidden(A_35,C_36)
      | ~ r1_tarski(k2_tarski(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_350,plain,(
    ! [A_49,B_50,B_51] : r2_hidden(A_49,k2_xboole_0(k2_tarski(A_49,B_50),B_51)) ),
    inference(resolution,[status(thm)],[c_8,c_243])).

tff(c_372,plain,(
    ! [A_52,B_53] : r2_hidden(A_52,k2_xboole_0(k1_tarski(A_52),B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_350])).

tff(c_385,plain,(
    ! [A_54,B_55] : r2_hidden(A_54,k2_xboole_0(B_55,k1_tarski(A_54))) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_372])).

tff(c_388,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_385])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.24  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.04/1.24  
% 2.04/1.24  %Foreground sorts:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Background operators:
% 2.04/1.24  
% 2.04/1.24  
% 2.04/1.24  %Foreground operators:
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.04/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.24  
% 2.04/1.25  tff(f_52, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.04/1.25  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.04/1.25  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.04/1.25  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.04/1.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.25  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.25  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.04/1.25  tff(c_24, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.25  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.25  tff(c_72, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.25  tff(c_124, plain, (![B_27, A_28]: (k3_tarski(k2_tarski(B_27, A_28))=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_10, c_72])).
% 2.04/1.25  tff(c_16, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.25  tff(c_130, plain, (![B_27, A_28]: (k2_xboole_0(B_27, A_28)=k2_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_124, c_16])).
% 2.04/1.25  tff(c_26, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.25  tff(c_150, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_26])).
% 2.04/1.25  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.25  tff(c_221, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_150, c_2])).
% 2.04/1.25  tff(c_224, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_221])).
% 2.04/1.25  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.25  tff(c_243, plain, (![A_35, C_36, B_37]: (r2_hidden(A_35, C_36) | ~r1_tarski(k2_tarski(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.25  tff(c_350, plain, (![A_49, B_50, B_51]: (r2_hidden(A_49, k2_xboole_0(k2_tarski(A_49, B_50), B_51)))), inference(resolution, [status(thm)], [c_8, c_243])).
% 2.04/1.25  tff(c_372, plain, (![A_52, B_53]: (r2_hidden(A_52, k2_xboole_0(k1_tarski(A_52), B_53)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_350])).
% 2.04/1.25  tff(c_385, plain, (![A_54, B_55]: (r2_hidden(A_54, k2_xboole_0(B_55, k1_tarski(A_54))))), inference(superposition, [status(thm), theory('equality')], [c_130, c_372])).
% 2.04/1.25  tff(c_388, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_224, c_385])).
% 2.04/1.25  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_388])).
% 2.04/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  Inference rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Ref     : 0
% 2.04/1.25  #Sup     : 92
% 2.04/1.25  #Fact    : 0
% 2.04/1.25  #Define  : 0
% 2.04/1.25  #Split   : 1
% 2.04/1.25  #Chain   : 0
% 2.04/1.25  #Close   : 0
% 2.04/1.25  
% 2.04/1.25  Ordering : KBO
% 2.04/1.25  
% 2.04/1.25  Simplification rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Subsume      : 6
% 2.04/1.25  #Demod        : 20
% 2.04/1.25  #Tautology    : 49
% 2.04/1.25  #SimpNegUnit  : 1
% 2.04/1.25  #BackRed      : 2
% 2.04/1.25  
% 2.04/1.25  #Partial instantiations: 0
% 2.04/1.25  #Strategies tried      : 1
% 2.04/1.25  
% 2.04/1.25  Timing (in seconds)
% 2.04/1.25  ----------------------
% 2.04/1.26  Preprocessing        : 0.28
% 2.04/1.26  Parsing              : 0.15
% 2.04/1.26  CNF conversion       : 0.02
% 2.04/1.26  Main loop            : 0.21
% 2.04/1.26  Inferencing          : 0.07
% 2.04/1.26  Reduction            : 0.08
% 2.04/1.26  Demodulation         : 0.06
% 2.04/1.26  BG Simplification    : 0.01
% 2.04/1.26  Subsumption          : 0.04
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.52
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
