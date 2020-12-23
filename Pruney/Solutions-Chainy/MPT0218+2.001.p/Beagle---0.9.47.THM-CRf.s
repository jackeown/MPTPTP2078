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
% DateTime   : Thu Dec  3 09:47:46 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    5 (   5 expanded)
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
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_83,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(A_24,k2_xboole_0(C_25,B_26))
      | ~ r1_tarski(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_32,A_33,B_34] :
      ( r1_tarski(A_32,k2_tarski(A_33,B_34))
      | ~ r1_tarski(A_32,k1_tarski(B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_123,plain,(
    ! [A_35,A_36,B_37] :
      ( r1_tarski(A_35,k2_tarski(A_36,B_37))
      | ~ r1_tarski(A_35,k1_tarski(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_106])).

tff(c_20,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_128,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_20])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.74/1.17  
% 1.74/1.17  %Foreground sorts:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Background operators:
% 1.74/1.17  
% 1.74/1.17  
% 1.74/1.17  %Foreground operators:
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.74/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.74/1.17  
% 1.74/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.74/1.17  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.74/1.17  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.74/1.17  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.74/1.17  tff(f_48, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.74/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.17  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.74/1.17  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.17  tff(c_83, plain, (![A_24, C_25, B_26]: (r1_tarski(A_24, k2_xboole_0(C_25, B_26)) | ~r1_tarski(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.17  tff(c_106, plain, (![A_32, A_33, B_34]: (r1_tarski(A_32, k2_tarski(A_33, B_34)) | ~r1_tarski(A_32, k1_tarski(B_34)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_83])).
% 1.74/1.17  tff(c_123, plain, (![A_35, A_36, B_37]: (r1_tarski(A_35, k2_tarski(A_36, B_37)) | ~r1_tarski(A_35, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_106])).
% 1.74/1.17  tff(c_20, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.17  tff(c_128, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_123, c_20])).
% 1.74/1.17  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_128])).
% 1.74/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.17  
% 1.74/1.17  Inference rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Ref     : 0
% 1.74/1.17  #Sup     : 29
% 1.74/1.17  #Fact    : 0
% 1.74/1.17  #Define  : 0
% 1.74/1.17  #Split   : 0
% 1.74/1.17  #Chain   : 0
% 1.74/1.17  #Close   : 0
% 1.74/1.17  
% 1.74/1.17  Ordering : KBO
% 1.74/1.17  
% 1.74/1.17  Simplification rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Subsume      : 0
% 1.74/1.17  #Demod        : 3
% 1.74/1.17  #Tautology    : 19
% 1.74/1.17  #SimpNegUnit  : 0
% 1.74/1.17  #BackRed      : 0
% 1.74/1.17  
% 1.74/1.17  #Partial instantiations: 0
% 1.74/1.17  #Strategies tried      : 1
% 1.74/1.17  
% 1.74/1.17  Timing (in seconds)
% 1.74/1.17  ----------------------
% 1.74/1.18  Preprocessing        : 0.28
% 1.74/1.18  Parsing              : 0.15
% 1.74/1.18  CNF conversion       : 0.02
% 1.74/1.18  Main loop            : 0.11
% 1.74/1.18  Inferencing          : 0.04
% 1.74/1.18  Reduction            : 0.04
% 1.74/1.18  Demodulation         : 0.03
% 1.74/1.18  BG Simplification    : 0.01
% 1.74/1.18  Subsumption          : 0.02
% 1.74/1.18  Abstraction          : 0.01
% 1.74/1.18  MUC search           : 0.00
% 1.74/1.18  Cooper               : 0.00
% 1.74/1.18  Total                : 0.41
% 1.74/1.18  Index Insertion      : 0.00
% 1.74/1.18  Index Deletion       : 0.00
% 1.74/1.18  Index Matching       : 0.00
% 1.74/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
