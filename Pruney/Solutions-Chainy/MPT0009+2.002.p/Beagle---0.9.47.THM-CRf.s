%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:28 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_2'(A_15,B_16),A_15)
      | r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_18,B_19] :
      ( ~ v1_xboole_0(A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_22,c_2])).

tff(c_14,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33,c_14])).

tff(c_40,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.06  
% 1.49/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.07  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.49/1.07  
% 1.49/1.07  %Foreground sorts:
% 1.49/1.07  
% 1.49/1.07  
% 1.49/1.07  %Background operators:
% 1.49/1.07  
% 1.49/1.07  
% 1.49/1.07  %Foreground operators:
% 1.49/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.49/1.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.49/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.49/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.49/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.49/1.07  
% 1.49/1.07  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.49/1.07  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.49/1.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.49/1.07  tff(f_42, negated_conjecture, ~(![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.49/1.07  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.07  tff(c_22, plain, (![A_15, B_16]: (r2_hidden('#skF_2'(A_15, B_16), A_15) | r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.49/1.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.49/1.07  tff(c_33, plain, (![A_18, B_19]: (~v1_xboole_0(A_18) | r1_tarski(A_18, B_19))), inference(resolution, [status(thm)], [c_22, c_2])).
% 1.49/1.07  tff(c_14, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.49/1.07  tff(c_36, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_14])).
% 1.49/1.07  tff(c_40, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 1.49/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.07  
% 1.49/1.07  Inference rules
% 1.49/1.07  ----------------------
% 1.49/1.07  #Ref     : 0
% 1.49/1.07  #Sup     : 4
% 1.49/1.07  #Fact    : 0
% 1.49/1.07  #Define  : 0
% 1.49/1.07  #Split   : 0
% 1.49/1.07  #Chain   : 0
% 1.49/1.07  #Close   : 0
% 1.49/1.07  
% 1.49/1.07  Ordering : KBO
% 1.49/1.07  
% 1.49/1.07  Simplification rules
% 1.49/1.07  ----------------------
% 1.49/1.07  #Subsume      : 0
% 1.49/1.07  #Demod        : 1
% 1.49/1.07  #Tautology    : 1
% 1.49/1.07  #SimpNegUnit  : 0
% 1.49/1.07  #BackRed      : 0
% 1.49/1.07  
% 1.49/1.07  #Partial instantiations: 0
% 1.49/1.07  #Strategies tried      : 1
% 1.49/1.07  
% 1.49/1.07  Timing (in seconds)
% 1.49/1.07  ----------------------
% 1.49/1.08  Preprocessing        : 0.24
% 1.49/1.08  Parsing              : 0.13
% 1.49/1.08  CNF conversion       : 0.02
% 1.49/1.08  Main loop            : 0.08
% 1.49/1.08  Inferencing          : 0.04
% 1.49/1.08  Reduction            : 0.02
% 1.49/1.08  Demodulation         : 0.01
% 1.49/1.08  BG Simplification    : 0.01
% 1.49/1.08  Subsumption          : 0.01
% 1.49/1.08  Abstraction          : 0.00
% 1.49/1.08  MUC search           : 0.00
% 1.49/1.08  Cooper               : 0.00
% 1.49/1.08  Total                : 0.35
% 1.49/1.08  Index Insertion      : 0.00
% 1.49/1.08  Index Deletion       : 0.00
% 1.49/1.08  Index Matching       : 0.00
% 1.61/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
