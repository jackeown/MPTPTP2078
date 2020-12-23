%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:28 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( r1_tarski(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_49,plain,(
    ! [C_24,B_25,A_26] :
      ( r2_hidden(C_24,B_25)
      | ~ r2_hidden(C_24,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_3'(A_27),B_28)
      | ~ r1_tarski(A_27,B_28)
      | k1_xboole_0 = A_27 ) ),
    inference(resolution,[status(thm)],[c_14,c_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [B_29,A_30] :
      ( ~ v1_xboole_0(B_29)
      | ~ r1_tarski(A_30,B_29)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_76,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 1.66/1.10  
% 1.66/1.10  %Foreground sorts:
% 1.66/1.10  
% 1.66/1.10  
% 1.66/1.10  %Background operators:
% 1.66/1.10  
% 1.66/1.10  
% 1.66/1.10  %Foreground operators:
% 1.66/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.10  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.66/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.10  
% 1.66/1.10  tff(f_52, negated_conjecture, ~(![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.66/1.10  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.66/1.10  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.66/1.10  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.66/1.10  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.66/1.10  tff(c_16, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.10  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.66/1.10  tff(c_18, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.10  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.10  tff(c_49, plain, (![C_24, B_25, A_26]: (r2_hidden(C_24, B_25) | ~r2_hidden(C_24, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.10  tff(c_59, plain, (![A_27, B_28]: (r2_hidden('#skF_3'(A_27), B_28) | ~r1_tarski(A_27, B_28) | k1_xboole_0=A_27)), inference(resolution, [status(thm)], [c_14, c_49])).
% 1.66/1.10  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.10  tff(c_67, plain, (![B_29, A_30]: (~v1_xboole_0(B_29) | ~r1_tarski(A_30, B_29) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_59, c_2])).
% 1.66/1.10  tff(c_76, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_18, c_67])).
% 1.66/1.10  tff(c_81, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_76])).
% 1.66/1.10  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_81])).
% 1.66/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  Inference rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Ref     : 0
% 1.66/1.10  #Sup     : 13
% 1.66/1.10  #Fact    : 0
% 1.66/1.10  #Define  : 0
% 1.66/1.10  #Split   : 0
% 1.66/1.11  #Chain   : 0
% 1.66/1.11  #Close   : 0
% 1.66/1.11  
% 1.66/1.11  Ordering : KBO
% 1.66/1.11  
% 1.66/1.11  Simplification rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Subsume      : 2
% 1.66/1.11  #Demod        : 1
% 1.66/1.11  #Tautology    : 2
% 1.66/1.11  #SimpNegUnit  : 1
% 1.66/1.11  #BackRed      : 0
% 1.66/1.11  
% 1.66/1.11  #Partial instantiations: 0
% 1.66/1.11  #Strategies tried      : 1
% 1.66/1.11  
% 1.66/1.11  Timing (in seconds)
% 1.66/1.11  ----------------------
% 1.66/1.11  Preprocessing        : 0.25
% 1.66/1.11  Parsing              : 0.13
% 1.66/1.11  CNF conversion       : 0.02
% 1.66/1.11  Main loop            : 0.10
% 1.66/1.11  Inferencing          : 0.04
% 1.66/1.11  Reduction            : 0.02
% 1.66/1.11  Demodulation         : 0.02
% 1.66/1.11  BG Simplification    : 0.01
% 1.66/1.11  Subsumption          : 0.02
% 1.66/1.11  Abstraction          : 0.00
% 1.66/1.11  MUC search           : 0.00
% 1.66/1.11  Cooper               : 0.00
% 1.66/1.11  Total                : 0.37
% 1.66/1.11  Index Insertion      : 0.00
% 1.66/1.11  Index Deletion       : 0.00
% 1.66/1.11  Index Matching       : 0.00
% 1.66/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
