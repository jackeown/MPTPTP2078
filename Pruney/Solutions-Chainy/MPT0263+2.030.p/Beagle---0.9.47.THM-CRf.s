%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  28 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_69,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_16])).

tff(c_83,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(k1_tarski(A_21),B_22) = B_22
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(k1_tarski(A_23),B_24) = k1_tarski(A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [B_25,A_26] :
      ( k3_xboole_0(B_25,k1_tarski(A_26)) = k1_tarski(A_26)
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2])).

tff(c_14,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_138,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_17])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.26  
% 1.71/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.27  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.71/1.27  
% 1.71/1.27  %Foreground sorts:
% 1.71/1.27  
% 1.71/1.27  
% 1.71/1.27  %Background operators:
% 1.71/1.27  
% 1.71/1.27  
% 1.71/1.27  %Foreground operators:
% 1.71/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.27  
% 1.71/1.27  tff(f_42, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.71/1.27  tff(f_47, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.71/1.27  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.71/1.27  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.71/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.71/1.27  tff(c_69, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.27  tff(c_16, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.71/1.27  tff(c_73, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_69, c_16])).
% 1.71/1.27  tff(c_83, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), B_22)=B_22 | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.27  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.27  tff(c_95, plain, (![A_23, B_24]: (k3_xboole_0(k1_tarski(A_23), B_24)=k1_tarski(A_23) | ~r2_hidden(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_83, c_4])).
% 1.71/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.27  tff(c_128, plain, (![B_25, A_26]: (k3_xboole_0(B_25, k1_tarski(A_26))=k1_tarski(A_26) | ~r2_hidden(A_26, B_25))), inference(superposition, [status(thm), theory('equality')], [c_95, c_2])).
% 1.71/1.27  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.71/1.27  tff(c_17, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.71/1.27  tff(c_138, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_17])).
% 1.71/1.27  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_138])).
% 1.71/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.27  
% 1.71/1.27  Inference rules
% 1.71/1.27  ----------------------
% 1.71/1.27  #Ref     : 0
% 1.71/1.27  #Sup     : 35
% 1.71/1.27  #Fact    : 0
% 1.71/1.27  #Define  : 0
% 1.71/1.27  #Split   : 0
% 1.71/1.27  #Chain   : 0
% 1.71/1.27  #Close   : 0
% 1.71/1.27  
% 1.71/1.27  Ordering : KBO
% 1.71/1.27  
% 1.71/1.27  Simplification rules
% 1.71/1.27  ----------------------
% 1.71/1.27  #Subsume      : 0
% 1.71/1.27  #Demod        : 2
% 1.71/1.27  #Tautology    : 21
% 1.71/1.27  #SimpNegUnit  : 0
% 1.71/1.27  #BackRed      : 0
% 1.71/1.27  
% 1.71/1.27  #Partial instantiations: 0
% 1.71/1.27  #Strategies tried      : 1
% 1.71/1.27  
% 1.71/1.27  Timing (in seconds)
% 1.71/1.27  ----------------------
% 1.71/1.28  Preprocessing        : 0.29
% 1.71/1.28  Parsing              : 0.15
% 1.71/1.28  CNF conversion       : 0.01
% 1.71/1.28  Main loop            : 0.11
% 1.71/1.28  Inferencing          : 0.05
% 1.71/1.28  Reduction            : 0.03
% 1.71/1.28  Demodulation         : 0.03
% 1.71/1.28  BG Simplification    : 0.01
% 1.71/1.28  Subsumption          : 0.01
% 1.71/1.28  Abstraction          : 0.01
% 1.71/1.28  MUC search           : 0.00
% 1.71/1.28  Cooper               : 0.00
% 1.71/1.28  Total                : 0.42
% 1.71/1.28  Index Insertion      : 0.00
% 1.71/1.28  Index Deletion       : 0.00
% 1.71/1.28  Index Matching       : 0.00
% 1.71/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
