%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:09 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(k1_tarski(A_15),k2_tarski(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k2_tarski(A_15,B_16)) = k2_tarski(A_15,B_16) ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_18,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.70/1.12  
% 1.70/1.12  %Foreground sorts:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Background operators:
% 1.70/1.12  
% 1.70/1.12  
% 1.70/1.12  %Foreground operators:
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.12  
% 1.70/1.12  tff(f_43, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.70/1.12  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.70/1.12  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.70/1.12  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), k2_tarski(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.70/1.12  tff(c_75, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.12  tff(c_83, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(A_15, B_16))=k2_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_16, c_75])).
% 1.70/1.12  tff(c_18, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.12  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_18])).
% 1.70/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.12  
% 1.70/1.12  Inference rules
% 1.70/1.12  ----------------------
% 1.70/1.12  #Ref     : 0
% 1.70/1.12  #Sup     : 31
% 1.70/1.12  #Fact    : 0
% 1.70/1.12  #Define  : 0
% 1.70/1.12  #Split   : 0
% 1.70/1.12  #Chain   : 0
% 1.70/1.12  #Close   : 0
% 1.70/1.12  
% 1.70/1.12  Ordering : KBO
% 1.70/1.12  
% 1.70/1.12  Simplification rules
% 1.70/1.12  ----------------------
% 1.70/1.12  #Subsume      : 0
% 1.70/1.12  #Demod        : 4
% 1.70/1.12  #Tautology    : 27
% 1.70/1.12  #SimpNegUnit  : 0
% 1.70/1.12  #BackRed      : 1
% 1.70/1.12  
% 1.70/1.12  #Partial instantiations: 0
% 1.70/1.12  #Strategies tried      : 1
% 1.70/1.12  
% 1.70/1.12  Timing (in seconds)
% 1.70/1.12  ----------------------
% 1.70/1.13  Preprocessing        : 0.27
% 1.70/1.13  Parsing              : 0.15
% 1.70/1.13  CNF conversion       : 0.01
% 1.70/1.13  Main loop            : 0.11
% 1.70/1.13  Inferencing          : 0.04
% 1.70/1.13  Reduction            : 0.03
% 1.70/1.13  Demodulation         : 0.03
% 1.70/1.13  BG Simplification    : 0.01
% 1.70/1.13  Subsumption          : 0.01
% 1.70/1.13  Abstraction          : 0.01
% 1.70/1.13  MUC search           : 0.00
% 1.70/1.13  Cooper               : 0.00
% 1.70/1.13  Total                : 0.39
% 1.70/1.13  Index Insertion      : 0.00
% 1.70/1.13  Index Deletion       : 0.00
% 1.70/1.13  Index Matching       : 0.00
% 1.70/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
