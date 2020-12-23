%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:18 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_62,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),B_21)
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_18])).

tff(c_91,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(B_27,k1_tarski(A_28)) = k1_tarski(A_28)
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_19,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_103,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_19])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.27  
% 1.83/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.28  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.83/1.28  
% 1.83/1.28  %Foreground sorts:
% 1.83/1.28  
% 1.83/1.28  
% 1.83/1.28  %Background operators:
% 1.83/1.28  
% 1.83/1.28  
% 1.83/1.28  %Foreground operators:
% 1.83/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.83/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.28  
% 1.83/1.28  tff(f_40, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.83/1.28  tff(f_49, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.83/1.28  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.83/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.83/1.28  tff(c_62, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), B_21) | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.28  tff(c_18, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.28  tff(c_66, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_18])).
% 1.83/1.28  tff(c_91, plain, (![B_27, A_28]: (k3_xboole_0(B_27, k1_tarski(A_28))=k1_tarski(A_28) | ~r2_hidden(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.28  tff(c_16, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.83/1.28  tff(c_19, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.83/1.28  tff(c_103, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_19])).
% 1.83/1.28  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_103])).
% 1.83/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.28  
% 1.83/1.28  Inference rules
% 1.83/1.28  ----------------------
% 1.83/1.28  #Ref     : 0
% 1.83/1.28  #Sup     : 24
% 1.83/1.28  #Fact    : 0
% 1.83/1.28  #Define  : 0
% 1.83/1.28  #Split   : 0
% 1.83/1.28  #Chain   : 0
% 1.83/1.28  #Close   : 0
% 1.83/1.28  
% 1.83/1.28  Ordering : KBO
% 1.83/1.28  
% 1.83/1.28  Simplification rules
% 1.83/1.28  ----------------------
% 1.83/1.28  #Subsume      : 0
% 1.83/1.28  #Demod        : 2
% 1.83/1.28  #Tautology    : 15
% 1.83/1.28  #SimpNegUnit  : 0
% 1.83/1.28  #BackRed      : 0
% 1.83/1.28  
% 1.83/1.28  #Partial instantiations: 0
% 1.83/1.28  #Strategies tried      : 1
% 1.83/1.28  
% 1.83/1.28  Timing (in seconds)
% 1.83/1.28  ----------------------
% 1.83/1.29  Preprocessing        : 0.33
% 1.83/1.29  Parsing              : 0.17
% 1.83/1.29  CNF conversion       : 0.02
% 1.83/1.29  Main loop            : 0.10
% 1.83/1.29  Inferencing          : 0.04
% 1.83/1.29  Reduction            : 0.03
% 1.83/1.29  Demodulation         : 0.03
% 1.83/1.29  BG Simplification    : 0.01
% 1.83/1.29  Subsumption          : 0.01
% 1.83/1.29  Abstraction          : 0.01
% 1.83/1.29  MUC search           : 0.00
% 1.83/1.29  Cooper               : 0.00
% 1.83/1.29  Total                : 0.46
% 1.83/1.29  Index Insertion      : 0.00
% 1.83/1.29  Index Deletion       : 0.00
% 1.83/1.29  Index Matching       : 0.00
% 1.83/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
