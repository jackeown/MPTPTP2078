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
% DateTime   : Thu Dec  3 09:43:15 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  29 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_tarski(A,B)
          & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_xboole_1)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19,plain,(
    ! [B_8,A_9] :
      ( ~ r2_xboole_0(B_8,A_9)
      | ~ r2_xboole_0(A_9,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_19])).

tff(c_26,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_23,c_22])).

tff(c_38,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_45,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_48,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:31:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.10  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_1
% 1.60/1.10  
% 1.60/1.10  %Foreground sorts:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Background operators:
% 1.60/1.10  
% 1.60/1.10  
% 1.60/1.10  %Foreground operators:
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.10  
% 1.60/1.11  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.60/1.11  tff(f_43, negated_conjecture, ~(![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.60/1.11  tff(f_37, axiom, (![A, B]: ~(r2_xboole_0(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_xboole_1)).
% 1.60/1.11  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.11  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.11  tff(c_23, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.11  tff(c_10, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.11  tff(c_19, plain, (![B_8, A_9]: (~r2_xboole_0(B_8, A_9) | ~r2_xboole_0(A_9, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.60/1.11  tff(c_22, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_19])).
% 1.60/1.11  tff(c_26, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_23, c_22])).
% 1.60/1.11  tff(c_38, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 1.60/1.11  tff(c_45, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 1.60/1.11  tff(c_48, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_45])).
% 1.60/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.11  
% 1.60/1.11  Inference rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Ref     : 0
% 1.60/1.11  #Sup     : 6
% 1.60/1.11  #Fact    : 0
% 1.60/1.11  #Define  : 0
% 1.60/1.11  #Split   : 0
% 1.60/1.11  #Chain   : 0
% 1.60/1.11  #Close   : 0
% 1.60/1.11  
% 1.60/1.11  Ordering : KBO
% 1.60/1.11  
% 1.60/1.11  Simplification rules
% 1.60/1.11  ----------------------
% 1.60/1.11  #Subsume      : 1
% 1.60/1.11  #Demod        : 5
% 1.60/1.11  #Tautology    : 2
% 1.60/1.11  #SimpNegUnit  : 1
% 1.60/1.11  #BackRed      : 4
% 1.60/1.11  
% 1.60/1.11  #Partial instantiations: 0
% 1.60/1.11  #Strategies tried      : 1
% 1.60/1.11  
% 1.60/1.11  Timing (in seconds)
% 1.60/1.11  ----------------------
% 1.60/1.11  Preprocessing        : 0.26
% 1.60/1.12  Parsing              : 0.14
% 1.60/1.12  CNF conversion       : 0.02
% 1.60/1.12  Main loop            : 0.08
% 1.60/1.12  Inferencing          : 0.04
% 1.60/1.12  Reduction            : 0.02
% 1.60/1.12  Demodulation         : 0.02
% 1.60/1.12  BG Simplification    : 0.01
% 1.60/1.12  Subsumption          : 0.02
% 1.60/1.12  Abstraction          : 0.00
% 1.60/1.12  MUC search           : 0.00
% 1.60/1.12  Cooper               : 0.00
% 1.60/1.12  Total                : 0.36
% 1.60/1.12  Index Insertion      : 0.00
% 1.60/1.12  Index Deletion       : 0.00
% 1.60/1.12  Index Matching       : 0.00
% 1.60/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
