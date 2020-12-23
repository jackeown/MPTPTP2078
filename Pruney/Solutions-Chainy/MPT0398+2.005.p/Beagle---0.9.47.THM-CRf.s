%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:31 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.55s
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
%$ r1_tarski > r1_setfam_1 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_setfam_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_setfam_1(A_5,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_1] : r1_setfam_1(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_8])).

tff(c_6,plain,(
    ~ r1_setfam_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:57:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.09  
% 1.55/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.09  %$ r1_tarski > r1_setfam_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.55/1.09  
% 1.55/1.09  %Foreground sorts:
% 1.55/1.09  
% 1.55/1.09  
% 1.55/1.09  %Background operators:
% 1.55/1.09  
% 1.55/1.09  
% 1.55/1.09  %Foreground operators:
% 1.55/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.09  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.55/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.09  
% 1.55/1.09  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.55/1.09  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => r1_setfam_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_setfam_1)).
% 1.55/1.09  tff(f_34, negated_conjecture, ~(![A]: r1_setfam_1(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_setfam_1)).
% 1.55/1.09  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.55/1.09  tff(c_8, plain, (![A_5, B_6]: (r1_setfam_1(A_5, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.09  tff(c_12, plain, (![A_1]: (r1_setfam_1(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_8])).
% 1.55/1.09  tff(c_6, plain, (~r1_setfam_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.55/1.09  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_6])).
% 1.55/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.09  
% 1.55/1.09  Inference rules
% 1.55/1.09  ----------------------
% 1.55/1.10  #Ref     : 0
% 1.55/1.10  #Sup     : 1
% 1.55/1.10  #Fact    : 0
% 1.55/1.10  #Define  : 0
% 1.55/1.10  #Split   : 0
% 1.55/1.10  #Chain   : 0
% 1.55/1.10  #Close   : 0
% 1.55/1.10  
% 1.55/1.10  Ordering : KBO
% 1.55/1.10  
% 1.55/1.10  Simplification rules
% 1.55/1.10  ----------------------
% 1.55/1.10  #Subsume      : 0
% 1.55/1.10  #Demod        : 1
% 1.55/1.10  #Tautology    : 0
% 1.55/1.10  #SimpNegUnit  : 0
% 1.55/1.10  #BackRed      : 1
% 1.55/1.10  
% 1.55/1.10  #Partial instantiations: 0
% 1.55/1.10  #Strategies tried      : 1
% 1.55/1.10  
% 1.55/1.10  Timing (in seconds)
% 1.55/1.10  ----------------------
% 1.55/1.10  Preprocessing        : 0.25
% 1.55/1.10  Parsing              : 0.14
% 1.55/1.10  CNF conversion       : 0.02
% 1.55/1.10  Main loop            : 0.06
% 1.55/1.10  Inferencing          : 0.03
% 1.55/1.10  Reduction            : 0.02
% 1.55/1.10  Demodulation         : 0.01
% 1.55/1.10  BG Simplification    : 0.01
% 1.55/1.10  Subsumption          : 0.00
% 1.55/1.10  Abstraction          : 0.00
% 1.55/1.10  MUC search           : 0.00
% 1.55/1.10  Cooper               : 0.00
% 1.55/1.10  Total                : 0.33
% 1.55/1.10  Index Insertion      : 0.00
% 1.55/1.10  Index Deletion       : 0.00
% 1.55/1.10  Index Matching       : 0.00
% 1.55/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
