%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:15 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
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

tff(f_37,axiom,(
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

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [B_6,A_7] :
      ( ~ r2_xboole_0(B_6,A_7)
      | ~ r2_xboole_0(A_7,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_17,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_14])).

tff(c_29,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_23,c_17])).

tff(c_39,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_45,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_10])).

tff(c_48,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.08  
% 1.51/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.08  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_1
% 1.51/1.08  
% 1.51/1.08  %Foreground sorts:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Background operators:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Foreground operators:
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.08  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.08  
% 1.51/1.09  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.51/1.09  tff(f_43, negated_conjecture, ~(![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.51/1.09  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.51/1.09  tff(c_6, plain, (![B_4]: (~r2_xboole_0(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.51/1.09  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.51/1.09  tff(c_23, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.51/1.09  tff(c_10, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.51/1.09  tff(c_14, plain, (![B_6, A_7]: (~r2_xboole_0(B_6, A_7) | ~r2_xboole_0(A_7, B_6))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.51/1.09  tff(c_17, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_14])).
% 1.51/1.09  tff(c_29, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_23, c_17])).
% 1.51/1.09  tff(c_39, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_29])).
% 1.51/1.09  tff(c_45, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_10])).
% 1.51/1.09  tff(c_48, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_45])).
% 1.51/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.09  
% 1.51/1.09  Inference rules
% 1.51/1.09  ----------------------
% 1.51/1.09  #Ref     : 0
% 1.51/1.09  #Sup     : 6
% 1.51/1.09  #Fact    : 0
% 1.51/1.09  #Define  : 0
% 1.51/1.09  #Split   : 0
% 1.51/1.09  #Chain   : 0
% 1.51/1.09  #Close   : 0
% 1.51/1.09  
% 1.51/1.09  Ordering : KBO
% 1.51/1.09  
% 1.51/1.09  Simplification rules
% 1.51/1.09  ----------------------
% 1.51/1.09  #Subsume      : 1
% 1.51/1.09  #Demod        : 5
% 1.51/1.09  #Tautology    : 2
% 1.51/1.09  #SimpNegUnit  : 1
% 1.51/1.09  #BackRed      : 4
% 1.51/1.09  
% 1.51/1.09  #Partial instantiations: 0
% 1.51/1.09  #Strategies tried      : 1
% 1.51/1.09  
% 1.51/1.09  Timing (in seconds)
% 1.51/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.24
% 1.63/1.09  Parsing              : 0.13
% 1.63/1.09  CNF conversion       : 0.01
% 1.63/1.10  Main loop            : 0.09
% 1.63/1.10  Inferencing          : 0.04
% 1.63/1.10  Reduction            : 0.02
% 1.63/1.10  Demodulation         : 0.02
% 1.63/1.10  BG Simplification    : 0.01
% 1.63/1.10  Subsumption          : 0.02
% 1.63/1.10  Abstraction          : 0.00
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.35
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
