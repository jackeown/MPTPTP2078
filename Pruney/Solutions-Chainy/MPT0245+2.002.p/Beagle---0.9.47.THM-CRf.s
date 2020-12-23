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
% DateTime   : Thu Dec  3 09:49:59 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => ( r2_hidden(C,A)
          | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r2_hidden(C,A)
        | r1_tarski(A,k4_xboole_0(B,k1_tarski(C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_zfmisc_1)).

tff(c_6,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,k4_xboole_0(B_5,k1_tarski(C_6)))
      | r2_hidden(C_6,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,
    ( r2_hidden('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_9,c_4])).

tff(c_15,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_17,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.10  
% 1.55/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.12  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.55/1.12  
% 1.55/1.12  %Foreground sorts:
% 1.55/1.12  
% 1.55/1.12  
% 1.55/1.12  %Background operators:
% 1.55/1.12  
% 1.55/1.12  
% 1.55/1.12  %Foreground operators:
% 1.55/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.55/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.55/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.12  
% 1.55/1.13  tff(f_38, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_zfmisc_1)).
% 1.55/1.13  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => (r2_hidden(C, A) | r1_tarski(A, k4_xboole_0(B, k1_tarski(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_zfmisc_1)).
% 1.55/1.13  tff(c_6, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.55/1.13  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.55/1.13  tff(c_9, plain, (![A_4, B_5, C_6]: (r1_tarski(A_4, k4_xboole_0(B_5, k1_tarski(C_6))) | r2_hidden(C_6, A_4) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.13  tff(c_4, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.55/1.13  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_1') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_9, c_4])).
% 1.55/1.13  tff(c_15, plain, (r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 1.55/1.13  tff(c_17, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_15])).
% 1.55/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.13  
% 1.55/1.13  Inference rules
% 1.55/1.13  ----------------------
% 1.55/1.13  #Ref     : 0
% 1.55/1.13  #Sup     : 1
% 1.55/1.13  #Fact    : 0
% 1.55/1.13  #Define  : 0
% 1.55/1.13  #Split   : 0
% 1.55/1.13  #Chain   : 0
% 1.55/1.13  #Close   : 0
% 1.55/1.13  
% 1.55/1.13  Ordering : KBO
% 1.55/1.13  
% 1.55/1.13  Simplification rules
% 1.55/1.13  ----------------------
% 1.55/1.13  #Subsume      : 0
% 1.55/1.13  #Demod        : 1
% 1.55/1.13  #Tautology    : 0
% 1.55/1.13  #SimpNegUnit  : 1
% 1.55/1.13  #BackRed      : 0
% 1.55/1.13  
% 1.55/1.13  #Partial instantiations: 0
% 1.55/1.13  #Strategies tried      : 1
% 1.55/1.13  
% 1.55/1.13  Timing (in seconds)
% 1.55/1.13  ----------------------
% 1.55/1.14  Preprocessing        : 0.23
% 1.55/1.14  Parsing              : 0.13
% 1.55/1.14  CNF conversion       : 0.01
% 1.55/1.14  Main loop            : 0.06
% 1.55/1.14  Inferencing          : 0.03
% 1.55/1.14  Reduction            : 0.01
% 1.55/1.14  Demodulation         : 0.01
% 1.55/1.14  BG Simplification    : 0.01
% 1.55/1.14  Subsumption          : 0.00
% 1.55/1.14  Abstraction          : 0.00
% 1.55/1.14  MUC search           : 0.00
% 1.55/1.14  Cooper               : 0.00
% 1.55/1.14  Total                : 0.33
% 1.55/1.14  Index Insertion      : 0.00
% 1.55/1.14  Index Deletion       : 0.00
% 1.55/1.14  Index Matching       : 0.00
% 1.55/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
