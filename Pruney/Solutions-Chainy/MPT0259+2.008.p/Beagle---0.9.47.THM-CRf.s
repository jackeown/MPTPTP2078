%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = A_34
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_57,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden(A_36,B_37)
      | k4_xboole_0(k1_tarski(A_36),B_37) != k1_tarski(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_57])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.52  
% 2.13/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.52  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.13/1.52  
% 2.13/1.52  %Foreground sorts:
% 2.13/1.52  
% 2.13/1.52  
% 2.13/1.52  %Background operators:
% 2.13/1.52  
% 2.13/1.52  
% 2.13/1.52  %Foreground operators:
% 2.13/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.52  
% 2.19/1.53  tff(f_52, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 2.19/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.19/1.53  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.19/1.53  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.53  tff(c_24, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.53  tff(c_44, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=A_34 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.53  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_24, c_44])).
% 2.19/1.53  tff(c_57, plain, (![A_36, B_37]: (~r2_hidden(A_36, B_37) | k4_xboole_0(k1_tarski(A_36), B_37)!=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.53  tff(c_60, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_52, c_57])).
% 2.19/1.53  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 2.19/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.53  
% 2.19/1.53  Inference rules
% 2.19/1.53  ----------------------
% 2.19/1.53  #Ref     : 0
% 2.19/1.53  #Sup     : 9
% 2.19/1.53  #Fact    : 0
% 2.19/1.53  #Define  : 0
% 2.19/1.53  #Split   : 0
% 2.19/1.53  #Chain   : 0
% 2.19/1.53  #Close   : 0
% 2.19/1.53  
% 2.19/1.53  Ordering : KBO
% 2.19/1.53  
% 2.19/1.53  Simplification rules
% 2.19/1.53  ----------------------
% 2.19/1.53  #Subsume      : 0
% 2.19/1.53  #Demod        : 1
% 2.19/1.53  #Tautology    : 7
% 2.19/1.53  #SimpNegUnit  : 0
% 2.19/1.53  #BackRed      : 0
% 2.19/1.53  
% 2.19/1.53  #Partial instantiations: 0
% 2.19/1.53  #Strategies tried      : 1
% 2.19/1.53  
% 2.19/1.53  Timing (in seconds)
% 2.19/1.53  ----------------------
% 2.19/1.54  Preprocessing        : 0.47
% 2.19/1.54  Parsing              : 0.24
% 2.19/1.54  CNF conversion       : 0.03
% 2.19/1.54  Main loop            : 0.13
% 2.19/1.54  Inferencing          : 0.05
% 2.19/1.54  Reduction            : 0.04
% 2.19/1.54  Demodulation         : 0.03
% 2.19/1.54  BG Simplification    : 0.02
% 2.19/1.54  Subsumption          : 0.01
% 2.19/1.54  Abstraction          : 0.01
% 2.19/1.54  MUC search           : 0.00
% 2.19/1.54  Cooper               : 0.00
% 2.19/1.54  Total                : 0.64
% 2.19/1.54  Index Insertion      : 0.00
% 2.19/1.54  Index Deletion       : 0.00
% 2.19/1.54  Index Matching       : 0.00
% 2.19/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
