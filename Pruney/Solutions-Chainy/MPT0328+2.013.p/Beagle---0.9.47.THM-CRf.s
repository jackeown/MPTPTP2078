%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:39 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
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
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,k1_tarski(B_13)) = A_12
      | r2_hidden(B_13,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k2_xboole_0(A_29,B_30),B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ~ r1_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_20])).

tff(c_116,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_119,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_116])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.09  
% 1.71/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.09  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.71/1.09  
% 1.71/1.09  %Foreground sorts:
% 1.71/1.09  
% 1.71/1.09  
% 1.71/1.09  %Background operators:
% 1.71/1.09  
% 1.71/1.09  
% 1.71/1.09  %Foreground operators:
% 1.71/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.09  
% 1.71/1.10  tff(f_52, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.71/1.10  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.71/1.10  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.71/1.10  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 1.71/1.10  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.71/1.10  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k1_tarski(B_13))=A_12 | r2_hidden(B_13, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.10  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.10  tff(c_85, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(A_29, B_30), B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.10  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.71/1.10  tff(c_111, plain, (~r1_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_20])).
% 1.71/1.10  tff(c_116, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(resolution, [status(thm)], [c_6, c_111])).
% 1.71/1.10  tff(c_119, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_116])).
% 1.71/1.10  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_119])).
% 1.71/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  Inference rules
% 1.71/1.10  ----------------------
% 1.71/1.10  #Ref     : 0
% 1.71/1.10  #Sup     : 23
% 1.71/1.10  #Fact    : 0
% 1.71/1.10  #Define  : 0
% 1.71/1.10  #Split   : 0
% 1.71/1.10  #Chain   : 0
% 1.71/1.10  #Close   : 0
% 1.71/1.10  
% 1.71/1.10  Ordering : KBO
% 1.71/1.10  
% 1.71/1.10  Simplification rules
% 1.71/1.10  ----------------------
% 1.71/1.10  #Subsume      : 0
% 1.71/1.10  #Demod        : 0
% 1.71/1.10  #Tautology    : 14
% 1.71/1.10  #SimpNegUnit  : 1
% 1.71/1.10  #BackRed      : 0
% 1.71/1.10  
% 1.71/1.10  #Partial instantiations: 0
% 1.71/1.10  #Strategies tried      : 1
% 1.71/1.10  
% 1.71/1.10  Timing (in seconds)
% 1.71/1.10  ----------------------
% 1.71/1.10  Preprocessing        : 0.27
% 1.71/1.10  Parsing              : 0.15
% 1.71/1.10  CNF conversion       : 0.01
% 1.71/1.10  Main loop            : 0.10
% 1.71/1.10  Inferencing          : 0.04
% 1.71/1.10  Reduction            : 0.03
% 1.71/1.10  Demodulation         : 0.02
% 1.71/1.10  BG Simplification    : 0.01
% 1.71/1.10  Subsumption          : 0.01
% 1.71/1.10  Abstraction          : 0.01
% 1.71/1.10  MUC search           : 0.00
% 1.71/1.10  Cooper               : 0.00
% 1.71/1.10  Total                : 0.39
% 1.71/1.10  Index Insertion      : 0.00
% 1.71/1.10  Index Deletion       : 0.00
% 1.71/1.10  Index Matching       : 0.00
% 1.71/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
