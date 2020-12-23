%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:06 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_12,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_31,plain,(
    ! [B_12,A_13] :
      ( k3_xboole_0(B_12,k1_tarski(A_13)) = k1_tarski(A_13)
      | ~ r2_hidden(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_10])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:43:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.06  
% 1.52/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.06  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.52/1.06  
% 1.52/1.06  %Foreground sorts:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Background operators:
% 1.52/1.06  
% 1.52/1.06  
% 1.52/1.06  %Foreground operators:
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.52/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.52/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.52/1.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.52/1.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.52/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.52/1.06  
% 1.52/1.07  tff(f_40, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.52/1.07  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.52/1.07  tff(c_12, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.52/1.07  tff(c_31, plain, (![B_12, A_13]: (k3_xboole_0(B_12, k1_tarski(A_13))=k1_tarski(A_13) | ~r2_hidden(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.52/1.07  tff(c_10, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.52/1.07  tff(c_37, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31, c_10])).
% 1.52/1.07  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_37])).
% 1.52/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  Inference rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Ref     : 0
% 1.52/1.07  #Sup     : 7
% 1.52/1.07  #Fact    : 0
% 1.52/1.07  #Define  : 0
% 1.52/1.07  #Split   : 0
% 1.52/1.07  #Chain   : 0
% 1.52/1.07  #Close   : 0
% 1.52/1.07  
% 1.52/1.07  Ordering : KBO
% 1.52/1.07  
% 1.52/1.07  Simplification rules
% 1.52/1.07  ----------------------
% 1.52/1.07  #Subsume      : 0
% 1.52/1.07  #Demod        : 1
% 1.52/1.07  #Tautology    : 5
% 1.52/1.07  #SimpNegUnit  : 0
% 1.52/1.07  #BackRed      : 0
% 1.52/1.07  
% 1.52/1.07  #Partial instantiations: 0
% 1.52/1.07  #Strategies tried      : 1
% 1.52/1.07  
% 1.52/1.07  Timing (in seconds)
% 1.52/1.07  ----------------------
% 1.52/1.07  Preprocessing        : 0.25
% 1.52/1.07  Parsing              : 0.13
% 1.52/1.07  CNF conversion       : 0.01
% 1.52/1.07  Main loop            : 0.06
% 1.52/1.07  Inferencing          : 0.03
% 1.52/1.07  Reduction            : 0.02
% 1.52/1.07  Demodulation         : 0.01
% 1.52/1.07  BG Simplification    : 0.01
% 1.52/1.07  Subsumption          : 0.00
% 1.52/1.07  Abstraction          : 0.01
% 1.52/1.07  MUC search           : 0.00
% 1.52/1.07  Cooper               : 0.00
% 1.52/1.07  Total                : 0.33
% 1.52/1.07  Index Insertion      : 0.00
% 1.52/1.07  Index Deletion       : 0.00
% 1.52/1.07  Index Matching       : 0.00
% 1.52/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
