%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_tarski(A_9)) = k1_ordinal1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ! [B_15,A_16] : k2_xboole_0(B_15,A_16) = k2_xboole_0(A_16,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(B_18,A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_88,plain,(
    ! [A_9] : r1_tarski(k1_tarski(A_9),k1_ordinal1(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [B_20,C_21,A_22] :
      ( r2_hidden(B_20,C_21)
      | ~ r1_tarski(k2_tarski(A_22,B_20),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    ! [A_26,C_27] :
      ( r2_hidden(A_26,C_27)
      | ~ r1_tarski(k1_tarski(A_26),C_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_133,plain,(
    ! [A_9] : r2_hidden(A_9,k1_ordinal1(A_9)) ),
    inference(resolution,[status(thm)],[c_88,c_117])).

tff(c_16,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1
% 1.63/1.13  
% 1.63/1.13  %Foreground sorts:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Background operators:
% 1.63/1.13  
% 1.63/1.13  
% 1.63/1.13  %Foreground operators:
% 1.63/1.13  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.13  
% 1.63/1.14  tff(f_39, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.63/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.63/1.14  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.63/1.14  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.63/1.14  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.63/1.14  tff(f_42, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.63/1.14  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_tarski(A_9))=k1_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.14  tff(c_40, plain, (![B_15, A_16]: (k2_xboole_0(B_15, A_16)=k2_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.14  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.14  tff(c_79, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(B_18, A_17)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 1.63/1.14  tff(c_88, plain, (![A_9]: (r1_tarski(k1_tarski(A_9), k1_ordinal1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_79])).
% 1.63/1.14  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.14  tff(c_93, plain, (![B_20, C_21, A_22]: (r2_hidden(B_20, C_21) | ~r1_tarski(k2_tarski(A_22, B_20), C_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.14  tff(c_117, plain, (![A_26, C_27]: (r2_hidden(A_26, C_27) | ~r1_tarski(k1_tarski(A_26), C_27))), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 1.63/1.14  tff(c_133, plain, (![A_9]: (r2_hidden(A_9, k1_ordinal1(A_9)))), inference(resolution, [status(thm)], [c_88, c_117])).
% 1.63/1.14  tff(c_16, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.14  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_16])).
% 1.63/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  Inference rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Ref     : 0
% 1.63/1.14  #Sup     : 27
% 1.63/1.14  #Fact    : 0
% 1.63/1.14  #Define  : 0
% 1.63/1.14  #Split   : 0
% 1.63/1.14  #Chain   : 0
% 1.63/1.14  #Close   : 0
% 1.63/1.14  
% 1.63/1.14  Ordering : KBO
% 1.63/1.14  
% 1.63/1.14  Simplification rules
% 1.63/1.14  ----------------------
% 1.63/1.14  #Subsume      : 0
% 1.63/1.14  #Demod        : 5
% 1.63/1.14  #Tautology    : 16
% 1.63/1.14  #SimpNegUnit  : 0
% 1.63/1.14  #BackRed      : 1
% 1.63/1.14  
% 1.63/1.14  #Partial instantiations: 0
% 1.63/1.14  #Strategies tried      : 1
% 1.63/1.14  
% 1.63/1.14  Timing (in seconds)
% 1.63/1.14  ----------------------
% 1.63/1.15  Preprocessing        : 0.26
% 1.63/1.15  Parsing              : 0.13
% 1.63/1.15  CNF conversion       : 0.01
% 1.63/1.15  Main loop            : 0.11
% 1.63/1.15  Inferencing          : 0.04
% 1.63/1.15  Reduction            : 0.04
% 1.63/1.15  Demodulation         : 0.03
% 1.63/1.15  BG Simplification    : 0.01
% 1.63/1.15  Subsumption          : 0.01
% 1.63/1.15  Abstraction          : 0.01
% 1.63/1.15  MUC search           : 0.00
% 1.63/1.15  Cooper               : 0.00
% 1.63/1.15  Total                : 0.40
% 1.63/1.15  Index Insertion      : 0.00
% 1.63/1.15  Index Deletion       : 0.00
% 1.63/1.15  Index Matching       : 0.00
% 1.63/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
