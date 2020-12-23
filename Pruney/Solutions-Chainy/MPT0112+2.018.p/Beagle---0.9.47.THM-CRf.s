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
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_8,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    ! [B_5,A_6] :
      ( ~ r2_xboole_0(B_5,A_6)
      | ~ r1_tarski(A_6,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_19,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_15])).

tff(c_27,plain,(
    k4_xboole_0('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_19])).

tff(c_32,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.21  
% 1.67/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.22  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.67/1.22  
% 1.67/1.22  %Foreground sorts:
% 1.67/1.22  
% 1.67/1.22  
% 1.67/1.22  %Background operators:
% 1.67/1.22  
% 1.67/1.22  
% 1.67/1.22  %Foreground operators:
% 1.67/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.22  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.67/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.22  
% 1.67/1.22  tff(f_40, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 1.67/1.22  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.67/1.22  tff(f_34, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.67/1.22  tff(c_8, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.22  tff(c_21, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.22  tff(c_10, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.67/1.22  tff(c_15, plain, (![B_5, A_6]: (~r2_xboole_0(B_5, A_6) | ~r1_tarski(A_6, B_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.22  tff(c_19, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_10, c_15])).
% 1.67/1.22  tff(c_27, plain, (k4_xboole_0('#skF_2', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_21, c_19])).
% 1.67/1.22  tff(c_32, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_27])).
% 1.67/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.22  
% 1.67/1.22  Inference rules
% 1.67/1.22  ----------------------
% 1.67/1.22  #Ref     : 0
% 1.67/1.22  #Sup     : 5
% 1.67/1.22  #Fact    : 0
% 1.67/1.22  #Define  : 0
% 1.67/1.22  #Split   : 0
% 1.67/1.22  #Chain   : 0
% 1.67/1.22  #Close   : 0
% 1.67/1.22  
% 1.67/1.22  Ordering : KBO
% 1.67/1.22  
% 1.67/1.22  Simplification rules
% 1.67/1.22  ----------------------
% 1.67/1.22  #Subsume      : 0
% 1.67/1.22  #Demod        : 1
% 1.67/1.22  #Tautology    : 3
% 1.67/1.22  #SimpNegUnit  : 0
% 1.67/1.22  #BackRed      : 0
% 1.67/1.22  
% 1.67/1.22  #Partial instantiations: 0
% 1.67/1.22  #Strategies tried      : 1
% 1.67/1.22  
% 1.67/1.22  Timing (in seconds)
% 1.67/1.22  ----------------------
% 1.67/1.23  Preprocessing        : 0.34
% 1.67/1.23  Parsing              : 0.20
% 1.67/1.23  CNF conversion       : 0.02
% 1.67/1.23  Main loop            : 0.07
% 1.67/1.23  Inferencing          : 0.04
% 1.67/1.23  Reduction            : 0.02
% 1.67/1.23  Demodulation         : 0.01
% 1.67/1.23  BG Simplification    : 0.01
% 1.67/1.23  Subsumption          : 0.01
% 1.67/1.23  Abstraction          : 0.00
% 1.67/1.23  MUC search           : 0.00
% 1.67/1.23  Cooper               : 0.00
% 1.67/1.23  Total                : 0.44
% 1.67/1.23  Index Insertion      : 0.00
% 1.67/1.23  Index Deletion       : 0.00
% 1.67/1.23  Index Matching       : 0.00
% 1.67/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
