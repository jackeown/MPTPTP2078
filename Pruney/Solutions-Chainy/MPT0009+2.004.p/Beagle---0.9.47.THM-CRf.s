%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:28 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_41,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19,plain,(
    ! [A_12,B_13] :
      ( ~ v1_xboole_0(A_12)
      | r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_10])).

tff(c_12,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_19,c_12])).

tff(c_26,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.06  
% 1.49/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.06  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.49/1.06  
% 1.49/1.06  %Foreground sorts:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Background operators:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Foreground operators:
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.49/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.49/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.49/1.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.49/1.06  
% 1.49/1.07  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.49/1.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.49/1.07  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 1.49/1.07  tff(f_41, negated_conjecture, ~(![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.49/1.07  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.49/1.07  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), A_10) | r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.49/1.07  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.49/1.07  tff(c_19, plain, (![A_12, B_13]: (~v1_xboole_0(A_12) | r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_14, c_10])).
% 1.49/1.07  tff(c_12, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.49/1.07  tff(c_22, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_19, c_12])).
% 1.49/1.07  tff(c_26, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_22])).
% 1.49/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.07  
% 1.49/1.07  Inference rules
% 1.49/1.07  ----------------------
% 1.49/1.07  #Ref     : 0
% 1.49/1.07  #Sup     : 2
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
% 1.49/1.07  #Tautology    : 0
% 1.49/1.07  #SimpNegUnit  : 0
% 1.49/1.07  #BackRed      : 0
% 1.49/1.07  
% 1.49/1.07  #Partial instantiations: 0
% 1.49/1.07  #Strategies tried      : 1
% 1.49/1.07  
% 1.49/1.07  Timing (in seconds)
% 1.49/1.07  ----------------------
% 1.49/1.07  Preprocessing        : 0.24
% 1.49/1.07  Parsing              : 0.13
% 1.49/1.07  CNF conversion       : 0.02
% 1.49/1.07  Main loop            : 0.07
% 1.49/1.07  Inferencing          : 0.04
% 1.49/1.07  Reduction            : 0.01
% 1.49/1.07  Demodulation         : 0.01
% 1.49/1.07  BG Simplification    : 0.01
% 1.49/1.07  Subsumption          : 0.01
% 1.49/1.07  Abstraction          : 0.00
% 1.49/1.07  MUC search           : 0.00
% 1.49/1.07  Cooper               : 0.00
% 1.49/1.07  Total                : 0.33
% 1.49/1.08  Index Insertion      : 0.00
% 1.49/1.08  Index Deletion       : 0.00
% 1.49/1.08  Index Matching       : 0.00
% 1.49/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
