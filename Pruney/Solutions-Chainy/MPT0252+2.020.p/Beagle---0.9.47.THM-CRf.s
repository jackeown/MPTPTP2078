%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  33 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_88,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,
    ( k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_36,c_88])).

tff(c_99,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_90])).

tff(c_39,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_33,B_32] : r1_tarski(A_33,k2_xboole_0(B_32,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_24])).

tff(c_111,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_54])).

tff(c_201,plain,(
    ! [A_46,C_47,B_48] :
      ( r2_hidden(A_46,C_47)
      | ~ r1_tarski(k2_tarski(A_46,B_48),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_204,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_201])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.85/1.22  
% 1.85/1.22  %Foreground sorts:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Background operators:
% 1.85/1.22  
% 1.85/1.22  
% 1.85/1.22  %Foreground operators:
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.22  
% 1.85/1.22  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.85/1.22  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.85/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.85/1.22  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.85/1.22  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.85/1.22  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.85/1.22  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.85/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.22  tff(c_34, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.85/1.22  tff(c_36, plain, (r1_tarski(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 1.85/1.22  tff(c_88, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.22  tff(c_90, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_36, c_88])).
% 1.85/1.22  tff(c_99, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_90])).
% 1.85/1.22  tff(c_39, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.22  tff(c_54, plain, (![A_33, B_32]: (r1_tarski(A_33, k2_xboole_0(B_32, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_39, c_24])).
% 1.85/1.22  tff(c_111, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_54])).
% 1.85/1.22  tff(c_201, plain, (![A_46, C_47, B_48]: (r2_hidden(A_46, C_47) | ~r1_tarski(k2_tarski(A_46, B_48), C_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.85/1.22  tff(c_204, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_111, c_201])).
% 1.85/1.22  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_204])).
% 1.85/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.22  
% 1.85/1.22  Inference rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Ref     : 0
% 1.85/1.22  #Sup     : 47
% 1.85/1.22  #Fact    : 0
% 1.85/1.22  #Define  : 0
% 1.85/1.22  #Split   : 0
% 1.85/1.22  #Chain   : 0
% 1.85/1.22  #Close   : 0
% 1.85/1.22  
% 1.85/1.22  Ordering : KBO
% 1.85/1.22  
% 1.85/1.22  Simplification rules
% 1.85/1.22  ----------------------
% 1.85/1.22  #Subsume      : 0
% 1.85/1.22  #Demod        : 15
% 1.85/1.22  #Tautology    : 24
% 1.85/1.22  #SimpNegUnit  : 1
% 1.85/1.22  #BackRed      : 1
% 1.85/1.22  
% 1.85/1.22  #Partial instantiations: 0
% 1.85/1.22  #Strategies tried      : 1
% 1.85/1.22  
% 1.85/1.22  Timing (in seconds)
% 1.85/1.22  ----------------------
% 1.85/1.23  Preprocessing        : 0.29
% 1.85/1.23  Parsing              : 0.16
% 1.85/1.23  CNF conversion       : 0.02
% 1.85/1.23  Main loop            : 0.17
% 1.85/1.23  Inferencing          : 0.05
% 1.85/1.23  Reduction            : 0.06
% 1.85/1.23  Demodulation         : 0.05
% 1.85/1.23  BG Simplification    : 0.01
% 1.85/1.23  Subsumption          : 0.03
% 1.85/1.23  Abstraction          : 0.01
% 1.85/1.23  MUC search           : 0.00
% 1.85/1.23  Cooper               : 0.00
% 1.85/1.23  Total                : 0.48
% 1.85/1.23  Index Insertion      : 0.00
% 1.85/1.23  Index Deletion       : 0.00
% 1.85/1.23  Index Matching       : 0.00
% 1.85/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
