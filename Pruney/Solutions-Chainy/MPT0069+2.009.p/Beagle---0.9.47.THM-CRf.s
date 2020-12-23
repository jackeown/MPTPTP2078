%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:17 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    r2_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [B_5,A_6] :
      ( ~ r2_xboole_0(B_5,A_6)
      | ~ r1_tarski(A_6,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_11,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_8])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.08  %$ r2_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_1
% 1.62/1.08  
% 1.62/1.08  %Foreground sorts:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Background operators:
% 1.62/1.08  
% 1.62/1.08  
% 1.62/1.08  %Foreground operators:
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.08  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.08  
% 1.62/1.09  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.62/1.09  tff(f_36, negated_conjecture, ~(![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_xboole_1)).
% 1.62/1.09  tff(f_32, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.62/1.09  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.09  tff(c_6, plain, (r2_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.09  tff(c_8, plain, (![B_5, A_6]: (~r2_xboole_0(B_5, A_6) | ~r1_tarski(A_6, B_5))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.09  tff(c_11, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_6, c_8])).
% 1.62/1.09  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_11])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 1
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 1
% 1.62/1.09  #Tautology    : 0
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.09  Preprocessing        : 0.24
% 1.62/1.09  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.01
% 1.62/1.10  Main loop            : 0.07
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.02
% 1.62/1.10  Demodulation         : 0.01
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.00
% 1.62/1.10  Abstraction          : 0.00
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.33
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
