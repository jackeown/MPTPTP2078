%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:04 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(c_16,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [B_30,A_31] :
      ( r2_hidden(B_30,A_31)
      | k3_xboole_0(A_31,k1_tarski(B_30)) != k1_tarski(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_57,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.67/1.09  
% 1.67/1.09  %Foreground sorts:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Background operators:
% 1.67/1.09  
% 1.67/1.09  
% 1.67/1.09  %Foreground operators:
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.09  
% 1.67/1.09  tff(f_46, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.67/1.09  tff(f_41, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 1.67/1.09  tff(c_16, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.09  tff(c_18, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.67/1.09  tff(c_50, plain, (![B_30, A_31]: (r2_hidden(B_30, A_31) | k3_xboole_0(A_31, k1_tarski(B_30))!=k1_tarski(B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.09  tff(c_53, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_50])).
% 1.67/1.09  tff(c_57, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_53])).
% 1.67/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.09  
% 1.67/1.09  Inference rules
% 1.67/1.09  ----------------------
% 1.67/1.09  #Ref     : 0
% 1.67/1.09  #Sup     : 9
% 1.67/1.09  #Fact    : 0
% 1.67/1.09  #Define  : 0
% 1.67/1.09  #Split   : 0
% 1.67/1.09  #Chain   : 0
% 1.67/1.09  #Close   : 0
% 1.67/1.09  
% 1.67/1.09  Ordering : KBO
% 1.67/1.09  
% 1.67/1.09  Simplification rules
% 1.67/1.09  ----------------------
% 1.67/1.09  #Subsume      : 0
% 1.67/1.09  #Demod        : 0
% 1.67/1.09  #Tautology    : 8
% 1.67/1.09  #SimpNegUnit  : 1
% 1.67/1.09  #BackRed      : 0
% 1.67/1.09  
% 1.67/1.09  #Partial instantiations: 0
% 1.67/1.09  #Strategies tried      : 1
% 1.67/1.09  
% 1.67/1.09  Timing (in seconds)
% 1.67/1.09  ----------------------
% 1.67/1.10  Preprocessing        : 0.28
% 1.67/1.10  Parsing              : 0.15
% 1.67/1.10  CNF conversion       : 0.01
% 1.67/1.10  Main loop            : 0.06
% 1.67/1.10  Inferencing          : 0.03
% 1.67/1.10  Reduction            : 0.02
% 1.67/1.10  Demodulation         : 0.01
% 1.67/1.10  BG Simplification    : 0.01
% 1.67/1.10  Subsumption          : 0.01
% 1.67/1.10  Abstraction          : 0.01
% 1.67/1.10  MUC search           : 0.00
% 1.67/1.10  Cooper               : 0.00
% 1.67/1.10  Total                : 0.36
% 1.67/1.10  Index Insertion      : 0.00
% 1.67/1.10  Index Deletion       : 0.00
% 1.67/1.10  Index Matching       : 0.00
% 1.67/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
