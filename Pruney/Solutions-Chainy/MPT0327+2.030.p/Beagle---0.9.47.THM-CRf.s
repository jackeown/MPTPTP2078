%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_18,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_99,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(k1_tarski(A_25),B_26) = B_26
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    ! [B_27,A_28] :
      ( k2_xboole_0(B_27,k1_tarski(A_28)) = B_27
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_20,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6,c_19])).

tff(c_146,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_20])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.22  
% 1.94/1.23  tff(f_46, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.94/1.23  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.94/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.94/1.23  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.94/1.23  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.23  tff(c_99, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)=B_26 | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.94/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.23  tff(c_130, plain, (![B_27, A_28]: (k2_xboole_0(B_27, k1_tarski(A_28))=B_27 | ~r2_hidden(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_99, c_2])).
% 1.94/1.23  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.23  tff(c_16, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.23  tff(c_19, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.94/1.23  tff(c_20, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6, c_19])).
% 1.94/1.23  tff(c_146, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_130, c_20])).
% 1.94/1.23  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_146])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 35
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 0
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 2
% 1.94/1.23  #Demod        : 4
% 1.94/1.23  #Tautology    : 21
% 1.94/1.23  #SimpNegUnit  : 0
% 1.94/1.23  #BackRed      : 0
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.30
% 1.94/1.23  Parsing              : 0.16
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.12
% 1.94/1.23  Inferencing          : 0.05
% 1.94/1.23  Reduction            : 0.04
% 1.94/1.23  Demodulation         : 0.03
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.02
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.44
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
