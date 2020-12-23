%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  38 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_14,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_1'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_21,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r1_tarski(C_19,B_18)
      | ~ r1_tarski(C_19,A_17)
      | v1_xboole_0(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_31,plain,(
    ! [C_20] :
      ( ~ r1_tarski(C_20,'#skF_2')
      | ~ r1_tarski(C_20,'#skF_3')
      | v1_xboole_0(C_20) ) ),
    inference(resolution,[status(thm)],[c_10,c_27])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_31])).

tff(c_42,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_38])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.40  
% 1.89/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.89/1.41  
% 1.89/1.41  %Foreground sorts:
% 1.89/1.41  
% 1.89/1.41  
% 1.89/1.41  %Background operators:
% 1.89/1.41  
% 1.89/1.41  
% 1.89/1.41  %Foreground operators:
% 1.89/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.41  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.41  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.41  
% 1.98/1.42  tff(f_51, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.98/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.98/1.42  tff(f_42, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.98/1.42  tff(c_14, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.42  tff(c_16, plain, (![A_11, B_12]: (~r2_hidden('#skF_1'(A_11, B_12), B_12) | r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.42  tff(c_21, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_16])).
% 1.98/1.42  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.42  tff(c_10, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.42  tff(c_27, plain, (![A_17, B_18, C_19]: (~r1_xboole_0(A_17, B_18) | ~r1_tarski(C_19, B_18) | ~r1_tarski(C_19, A_17) | v1_xboole_0(C_19))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.42  tff(c_31, plain, (![C_20]: (~r1_tarski(C_20, '#skF_2') | ~r1_tarski(C_20, '#skF_3') | v1_xboole_0(C_20))), inference(resolution, [status(thm)], [c_10, c_27])).
% 1.98/1.42  tff(c_38, plain, (~r1_tarski('#skF_3', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_31])).
% 1.98/1.42  tff(c_42, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21, c_38])).
% 1.98/1.42  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_42])).
% 1.98/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.42  
% 1.98/1.42  Inference rules
% 1.98/1.42  ----------------------
% 1.98/1.42  #Ref     : 0
% 1.98/1.42  #Sup     : 5
% 1.98/1.42  #Fact    : 0
% 1.98/1.42  #Define  : 0
% 1.98/1.42  #Split   : 0
% 1.98/1.42  #Chain   : 0
% 1.98/1.42  #Close   : 0
% 1.98/1.42  
% 1.98/1.42  Ordering : KBO
% 1.98/1.42  
% 1.98/1.42  Simplification rules
% 1.98/1.42  ----------------------
% 1.98/1.42  #Subsume      : 0
% 1.98/1.42  #Demod        : 1
% 1.98/1.42  #Tautology    : 0
% 1.98/1.42  #SimpNegUnit  : 1
% 1.98/1.42  #BackRed      : 0
% 1.98/1.42  
% 1.98/1.42  #Partial instantiations: 0
% 1.98/1.42  #Strategies tried      : 1
% 1.98/1.42  
% 1.98/1.42  Timing (in seconds)
% 1.98/1.42  ----------------------
% 1.98/1.43  Preprocessing        : 0.38
% 1.98/1.43  Parsing              : 0.20
% 1.98/1.43  CNF conversion       : 0.03
% 1.98/1.43  Main loop            : 0.16
% 1.98/1.43  Inferencing          : 0.08
% 1.98/1.43  Reduction            : 0.04
% 1.98/1.43  Demodulation         : 0.03
% 1.98/1.43  BG Simplification    : 0.02
% 1.98/1.43  Subsumption          : 0.02
% 1.98/1.43  Abstraction          : 0.01
% 1.98/1.43  MUC search           : 0.00
% 1.98/1.43  Cooper               : 0.00
% 1.98/1.43  Total                : 0.59
% 1.98/1.43  Index Insertion      : 0.00
% 1.98/1.43  Index Deletion       : 0.00
% 1.98/1.43  Index Matching       : 0.00
% 1.98/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
