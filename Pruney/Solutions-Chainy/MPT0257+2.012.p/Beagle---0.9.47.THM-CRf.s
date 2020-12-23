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
% DateTime   : Thu Dec  3 09:52:06 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [B_9,A_10] :
      ( k3_xboole_0(B_9,k1_tarski(A_10)) = k1_tarski(A_10)
      | ~ r2_hidden(A_10,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_8])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:25:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.37  
% 1.94/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.37  %$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.94/1.37  
% 1.94/1.37  %Foreground sorts:
% 1.94/1.37  
% 1.94/1.37  
% 1.94/1.37  %Background operators:
% 1.94/1.37  
% 1.94/1.37  
% 1.94/1.37  %Foreground operators:
% 1.94/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.37  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.37  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.37  
% 1.94/1.38  tff(f_38, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.94/1.38  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.94/1.38  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.38  tff(c_29, plain, (![B_9, A_10]: (k3_xboole_0(B_9, k1_tarski(A_10))=k1_tarski(A_10) | ~r2_hidden(A_10, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.38  tff(c_8, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.38  tff(c_35, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_29, c_8])).
% 1.94/1.38  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_35])).
% 1.94/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.38  
% 1.94/1.38  Inference rules
% 1.94/1.38  ----------------------
% 1.94/1.38  #Ref     : 0
% 1.94/1.38  #Sup     : 7
% 1.94/1.38  #Fact    : 0
% 1.94/1.38  #Define  : 0
% 1.94/1.38  #Split   : 0
% 1.94/1.38  #Chain   : 0
% 2.01/1.38  #Close   : 0
% 2.01/1.38  
% 2.01/1.38  Ordering : KBO
% 2.01/1.38  
% 2.01/1.38  Simplification rules
% 2.01/1.38  ----------------------
% 2.01/1.38  #Subsume      : 0
% 2.01/1.38  #Demod        : 1
% 2.01/1.38  #Tautology    : 5
% 2.01/1.38  #SimpNegUnit  : 0
% 2.01/1.38  #BackRed      : 0
% 2.01/1.38  
% 2.01/1.38  #Partial instantiations: 0
% 2.01/1.38  #Strategies tried      : 1
% 2.01/1.38  
% 2.01/1.38  Timing (in seconds)
% 2.01/1.38  ----------------------
% 2.01/1.39  Preprocessing        : 0.42
% 2.01/1.39  Parsing              : 0.22
% 2.01/1.39  CNF conversion       : 0.02
% 2.01/1.39  Main loop            : 0.11
% 2.01/1.39  Inferencing          : 0.05
% 2.01/1.39  Reduction            : 0.03
% 2.01/1.39  Demodulation         : 0.03
% 2.01/1.39  BG Simplification    : 0.01
% 2.01/1.39  Subsumption          : 0.01
% 2.01/1.39  Abstraction          : 0.01
% 2.01/1.39  MUC search           : 0.00
% 2.01/1.39  Cooper               : 0.00
% 2.01/1.39  Total                : 0.57
% 2.01/1.39  Index Insertion      : 0.00
% 2.01/1.39  Index Deletion       : 0.00
% 2.01/1.39  Index Matching       : 0.00
% 2.01/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
