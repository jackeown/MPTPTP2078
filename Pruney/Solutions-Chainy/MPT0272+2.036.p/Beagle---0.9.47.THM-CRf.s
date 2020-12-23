%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:10 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_71,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(k1_tarski(A_25),B_26) = k1_tarski(A_25)
      | r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_20])).

tff(c_53,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_tarski(A_21),B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(k1_tarski(A_27),B_28) = k1_xboole_0
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_22])).

tff(c_113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.16  
% 1.60/1.16  %Foreground sorts:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Background operators:
% 1.60/1.16  
% 1.60/1.16  
% 1.60/1.16  %Foreground operators:
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.60/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.60/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.60/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.60/1.16  
% 1.80/1.16  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.80/1.16  tff(f_49, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.80/1.16  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.80/1.16  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.80/1.16  tff(c_71, plain, (![A_25, B_26]: (k4_xboole_0(k1_tarski(A_25), B_26)=k1_tarski(A_25) | r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.80/1.16  tff(c_20, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.80/1.16  tff(c_85, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_71, c_20])).
% 1.80/1.16  tff(c_53, plain, (![A_21, B_22]: (r1_tarski(k1_tarski(A_21), B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.16  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.16  tff(c_88, plain, (![A_27, B_28]: (k4_xboole_0(k1_tarski(A_27), B_28)=k1_xboole_0 | ~r2_hidden(A_27, B_28))), inference(resolution, [status(thm)], [c_53, c_4])).
% 1.80/1.16  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.80/1.16  tff(c_100, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_22])).
% 1.80/1.16  tff(c_113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_100])).
% 1.80/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  Inference rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Ref     : 0
% 1.80/1.16  #Sup     : 20
% 1.80/1.16  #Fact    : 0
% 1.80/1.16  #Define  : 0
% 1.80/1.16  #Split   : 0
% 1.80/1.16  #Chain   : 0
% 1.80/1.16  #Close   : 0
% 1.80/1.16  
% 1.80/1.16  Ordering : KBO
% 1.80/1.16  
% 1.80/1.16  Simplification rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Subsume      : 0
% 1.80/1.16  #Demod        : 3
% 1.80/1.16  #Tautology    : 13
% 1.80/1.16  #SimpNegUnit  : 0
% 1.80/1.16  #BackRed      : 0
% 1.80/1.16  
% 1.80/1.16  #Partial instantiations: 0
% 1.80/1.16  #Strategies tried      : 1
% 1.80/1.16  
% 1.80/1.16  Timing (in seconds)
% 1.80/1.16  ----------------------
% 1.80/1.17  Preprocessing        : 0.27
% 1.80/1.17  Parsing              : 0.14
% 1.80/1.17  CNF conversion       : 0.02
% 1.80/1.17  Main loop            : 0.10
% 1.80/1.17  Inferencing          : 0.04
% 1.80/1.17  Reduction            : 0.03
% 1.80/1.17  Demodulation         : 0.02
% 1.80/1.17  BG Simplification    : 0.01
% 1.80/1.17  Subsumption          : 0.01
% 1.80/1.17  Abstraction          : 0.01
% 1.80/1.17  MUC search           : 0.00
% 1.80/1.17  Cooper               : 0.00
% 1.80/1.17  Total                : 0.39
% 1.80/1.17  Index Insertion      : 0.00
% 1.80/1.17  Index Deletion       : 0.00
% 1.80/1.17  Index Matching       : 0.00
% 1.80/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
