%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,k1_tarski(B_14)) = A_13
      | r2_hidden(B_14,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(k2_xboole_0(A_28,B_29),B_29) = A_28
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ~ r1_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_20])).

tff(c_108,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_111,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_108])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.15  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.78/1.15  
% 1.78/1.15  %Foreground sorts:
% 1.78/1.15  
% 1.78/1.15  
% 1.78/1.15  %Background operators:
% 1.78/1.15  
% 1.78/1.15  
% 1.78/1.15  %Foreground operators:
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.78/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.15  
% 1.78/1.16  tff(f_52, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.78/1.16  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.78/1.16  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.78/1.16  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.78/1.16  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.16  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k1_tarski(B_14))=A_13 | r2_hidden(B_14, A_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.16  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k4_xboole_0(A_1, B_2)!=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.16  tff(c_77, plain, (![A_28, B_29]: (k4_xboole_0(k2_xboole_0(A_28, B_29), B_29)=A_28 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.16  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.16  tff(c_103, plain, (~r1_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_20])).
% 1.78/1.16  tff(c_108, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(resolution, [status(thm)], [c_4, c_103])).
% 1.78/1.16  tff(c_111, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_108])).
% 1.78/1.16  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_111])).
% 1.78/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  Inference rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Ref     : 0
% 1.78/1.16  #Sup     : 21
% 1.78/1.16  #Fact    : 0
% 1.78/1.16  #Define  : 0
% 1.78/1.16  #Split   : 1
% 1.78/1.16  #Chain   : 0
% 1.78/1.16  #Close   : 0
% 1.78/1.16  
% 1.78/1.16  Ordering : KBO
% 1.78/1.16  
% 1.78/1.16  Simplification rules
% 1.78/1.16  ----------------------
% 1.78/1.16  #Subsume      : 0
% 1.78/1.16  #Demod        : 0
% 1.78/1.16  #Tautology    : 12
% 1.78/1.16  #SimpNegUnit  : 1
% 1.78/1.16  #BackRed      : 0
% 1.78/1.16  
% 1.78/1.16  #Partial instantiations: 0
% 1.78/1.16  #Strategies tried      : 1
% 1.78/1.16  
% 1.78/1.16  Timing (in seconds)
% 1.78/1.16  ----------------------
% 1.85/1.16  Preprocessing        : 0.29
% 1.85/1.16  Parsing              : 0.16
% 1.85/1.16  CNF conversion       : 0.02
% 1.85/1.16  Main loop            : 0.11
% 1.85/1.16  Inferencing          : 0.05
% 1.85/1.16  Reduction            : 0.03
% 1.85/1.16  Demodulation         : 0.02
% 1.85/1.16  BG Simplification    : 0.01
% 1.85/1.16  Subsumption          : 0.02
% 1.85/1.16  Abstraction          : 0.01
% 1.85/1.16  MUC search           : 0.00
% 1.85/1.16  Cooper               : 0.00
% 1.85/1.16  Total                : 0.42
% 1.85/1.16  Index Insertion      : 0.00
% 1.85/1.16  Index Deletion       : 0.00
% 1.85/1.16  Index Matching       : 0.00
% 1.85/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
