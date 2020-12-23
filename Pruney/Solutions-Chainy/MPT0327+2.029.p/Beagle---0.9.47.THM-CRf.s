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
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_16,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(k1_tarski(A_20),B_21) = B_21
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_24,A_25] :
      ( k2_xboole_0(A_24,k1_tarski(A_25)) = A_24
      | ~ r2_hidden(A_25,A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_18,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_17])).

tff(c_165,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.14  
% 1.62/1.15  tff(f_44, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.62/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.62/1.15  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.62/1.15  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.62/1.15  tff(c_16, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.15  tff(c_97, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)=B_21 | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.15  tff(c_145, plain, (![A_24, A_25]: (k2_xboole_0(A_24, k1_tarski(A_25))=A_24 | ~r2_hidden(A_25, A_24))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 1.62/1.15  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.15  tff(c_14, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.15  tff(c_17, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.62/1.15  tff(c_18, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_17])).
% 1.62/1.15  tff(c_165, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 1.62/1.15  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_165])).
% 1.62/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  Inference rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Ref     : 0
% 1.62/1.15  #Sup     : 42
% 1.62/1.15  #Fact    : 0
% 1.62/1.15  #Define  : 0
% 1.62/1.15  #Split   : 0
% 1.62/1.15  #Chain   : 0
% 1.62/1.15  #Close   : 0
% 1.62/1.15  
% 1.62/1.15  Ordering : KBO
% 1.62/1.15  
% 1.62/1.15  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 4
% 1.62/1.15  #Demod        : 4
% 1.62/1.15  #Tautology    : 21
% 1.62/1.15  #SimpNegUnit  : 0
% 1.62/1.15  #BackRed      : 0
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.15  Preprocessing        : 0.26
% 1.62/1.15  Parsing              : 0.14
% 1.62/1.15  CNF conversion       : 0.01
% 1.62/1.15  Main loop            : 0.12
% 1.62/1.15  Inferencing          : 0.05
% 1.62/1.15  Reduction            : 0.04
% 1.62/1.15  Demodulation         : 0.03
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.02
% 1.62/1.15  Abstraction          : 0.01
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.41
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
