%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  41 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_50,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_16,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_23,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(resolution,[status(thm)],[c_18,c_4])).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_29,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_xboole_0 = A_17
      | ~ r1_xboole_0(B_18,C_19)
      | ~ r1_tarski(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,'#skF_2')
      | ~ r1_tarski(A_20,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_40])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.12  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.12  
% 1.63/1.12  %Foreground sorts:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Background operators:
% 1.63/1.12  
% 1.63/1.12  
% 1.63/1.12  %Foreground operators:
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.63/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.12  
% 1.63/1.13  tff(f_50, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.63/1.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.63/1.13  tff(f_41, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.63/1.13  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.13  tff(c_16, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.63/1.13  tff(c_18, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.13  tff(c_23, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(resolution, [status(thm)], [c_18, c_4])).
% 1.63/1.13  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.63/1.13  tff(c_12, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.63/1.13  tff(c_29, plain, (![A_17, B_18, C_19]: (k1_xboole_0=A_17 | ~r1_xboole_0(B_18, C_19) | ~r1_tarski(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.63/1.13  tff(c_33, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, '#skF_2') | ~r1_tarski(A_20, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.63/1.13  tff(c_40, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_33])).
% 1.63/1.13  tff(c_44, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23, c_40])).
% 1.63/1.13  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.13  tff(c_47, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 1.63/1.13  tff(c_49, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_47])).
% 1.63/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.13  
% 1.63/1.13  Inference rules
% 1.63/1.13  ----------------------
% 1.63/1.13  #Ref     : 0
% 1.63/1.13  #Sup     : 5
% 1.63/1.13  #Fact    : 0
% 1.63/1.13  #Define  : 0
% 1.63/1.13  #Split   : 0
% 1.63/1.13  #Chain   : 0
% 1.63/1.13  #Close   : 0
% 1.63/1.13  
% 1.63/1.13  Ordering : KBO
% 1.63/1.13  
% 1.63/1.13  Simplification rules
% 1.63/1.13  ----------------------
% 1.63/1.13  #Subsume      : 0
% 1.63/1.13  #Demod        : 4
% 1.63/1.13  #Tautology    : 0
% 1.63/1.13  #SimpNegUnit  : 1
% 1.63/1.13  #BackRed      : 3
% 1.63/1.13  
% 1.63/1.13  #Partial instantiations: 0
% 1.63/1.13  #Strategies tried      : 1
% 1.63/1.13  
% 1.63/1.13  Timing (in seconds)
% 1.63/1.13  ----------------------
% 1.63/1.13  Preprocessing        : 0.27
% 1.63/1.13  Parsing              : 0.15
% 1.63/1.13  CNF conversion       : 0.02
% 1.63/1.13  Main loop            : 0.10
% 1.63/1.13  Inferencing          : 0.05
% 1.63/1.13  Reduction            : 0.02
% 1.63/1.13  Demodulation         : 0.02
% 1.63/1.13  BG Simplification    : 0.01
% 1.63/1.13  Subsumption          : 0.02
% 1.63/1.13  Abstraction          : 0.00
% 1.63/1.13  MUC search           : 0.00
% 1.63/1.13  Cooper               : 0.00
% 1.63/1.14  Total                : 0.39
% 1.63/1.14  Index Insertion      : 0.00
% 1.63/1.14  Index Deletion       : 0.00
% 1.63/1.14  Index Matching       : 0.00
% 1.63/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
