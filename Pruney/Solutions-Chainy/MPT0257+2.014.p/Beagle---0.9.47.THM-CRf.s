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
% DateTime   : Thu Dec  3 09:52:06 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
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
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [B_7,A_8] :
      ( k3_xboole_0(B_7,k1_tarski(A_8)) = k1_tarski(A_8)
      | ~ r2_hidden(A_8,B_7) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:52:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.09  
% 1.58/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.10  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.58/1.10  
% 1.58/1.10  %Foreground sorts:
% 1.58/1.10  
% 1.58/1.10  
% 1.58/1.10  %Background operators:
% 1.58/1.10  
% 1.58/1.10  
% 1.58/1.10  %Foreground operators:
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.58/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.58/1.10  
% 1.58/1.10  tff(f_38, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.58/1.10  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.58/1.10  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.58/1.10  tff(c_29, plain, (![B_7, A_8]: (k3_xboole_0(B_7, k1_tarski(A_8))=k1_tarski(A_8) | ~r2_hidden(A_8, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.10  tff(c_8, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.58/1.10  tff(c_35, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_29, c_8])).
% 1.58/1.10  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_35])).
% 1.58/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.10  
% 1.58/1.10  Inference rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Ref     : 0
% 1.58/1.10  #Sup     : 7
% 1.58/1.10  #Fact    : 0
% 1.58/1.10  #Define  : 0
% 1.58/1.10  #Split   : 0
% 1.58/1.10  #Chain   : 0
% 1.58/1.10  #Close   : 0
% 1.58/1.10  
% 1.58/1.10  Ordering : KBO
% 1.58/1.10  
% 1.58/1.10  Simplification rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Subsume      : 0
% 1.58/1.10  #Demod        : 1
% 1.58/1.10  #Tautology    : 5
% 1.58/1.10  #SimpNegUnit  : 0
% 1.58/1.10  #BackRed      : 0
% 1.58/1.10  
% 1.58/1.10  #Partial instantiations: 0
% 1.58/1.10  #Strategies tried      : 1
% 1.58/1.10  
% 1.58/1.10  Timing (in seconds)
% 1.58/1.10  ----------------------
% 1.58/1.10  Preprocessing        : 0.26
% 1.58/1.10  Parsing              : 0.14
% 1.58/1.10  CNF conversion       : 0.01
% 1.58/1.10  Main loop            : 0.06
% 1.58/1.10  Inferencing          : 0.03
% 1.58/1.11  Reduction            : 0.01
% 1.58/1.11  Demodulation         : 0.01
% 1.58/1.11  BG Simplification    : 0.01
% 1.58/1.11  Subsumption          : 0.00
% 1.58/1.11  Abstraction          : 0.01
% 1.58/1.11  MUC search           : 0.00
% 1.58/1.11  Cooper               : 0.00
% 1.58/1.11  Total                : 0.34
% 1.58/1.11  Index Insertion      : 0.00
% 1.58/1.11  Index Deletion       : 0.00
% 1.58/1.11  Index Matching       : 0.00
% 1.58/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
