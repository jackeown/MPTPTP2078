%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:44 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_18,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | ~ r1_tarski(k1_tarski(A_16),B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_16,B_7] : r2_hidden(A_16,k2_xboole_0(k1_tarski(A_16),B_7)) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_66,plain,(
    ! [C_30,B_31,A_32] :
      ( r2_hidden(C_30,B_31)
      | ~ r2_hidden(C_30,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_33,B_34,B_35] :
      ( r2_hidden(A_33,B_34)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_33),B_35),B_34) ) ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_83,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:06:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.06  
% 1.66/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.07  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.66/1.07  
% 1.66/1.07  %Foreground sorts:
% 1.66/1.07  
% 1.66/1.07  
% 1.66/1.07  %Background operators:
% 1.66/1.07  
% 1.66/1.07  
% 1.66/1.07  %Foreground operators:
% 1.66/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.07  
% 1.70/1.07  tff(f_47, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.70/1.07  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.70/1.07  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.70/1.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.70/1.07  tff(c_18, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.07  tff(c_20, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.07  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.07  tff(c_31, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | ~r1_tarski(k1_tarski(A_16), B_17))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.07  tff(c_36, plain, (![A_16, B_7]: (r2_hidden(A_16, k2_xboole_0(k1_tarski(A_16), B_7)))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.70/1.07  tff(c_66, plain, (![C_30, B_31, A_32]: (r2_hidden(C_30, B_31) | ~r2_hidden(C_30, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.70/1.07  tff(c_76, plain, (![A_33, B_34, B_35]: (r2_hidden(A_33, B_34) | ~r1_tarski(k2_xboole_0(k1_tarski(A_33), B_35), B_34))), inference(resolution, [status(thm)], [c_36, c_66])).
% 1.70/1.07  tff(c_83, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_76])).
% 1.70/1.07  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_83])).
% 1.70/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.07  
% 1.70/1.07  Inference rules
% 1.70/1.07  ----------------------
% 1.70/1.07  #Ref     : 0
% 1.70/1.07  #Sup     : 14
% 1.70/1.07  #Fact    : 0
% 1.70/1.07  #Define  : 0
% 1.70/1.07  #Split   : 0
% 1.70/1.07  #Chain   : 0
% 1.70/1.07  #Close   : 0
% 1.70/1.07  
% 1.70/1.07  Ordering : KBO
% 1.70/1.07  
% 1.70/1.07  Simplification rules
% 1.70/1.07  ----------------------
% 1.70/1.07  #Subsume      : 1
% 1.70/1.07  #Demod        : 1
% 1.70/1.07  #Tautology    : 6
% 1.70/1.07  #SimpNegUnit  : 1
% 1.70/1.07  #BackRed      : 0
% 1.70/1.07  
% 1.70/1.07  #Partial instantiations: 0
% 1.70/1.07  #Strategies tried      : 1
% 1.70/1.07  
% 1.70/1.07  Timing (in seconds)
% 1.70/1.07  ----------------------
% 1.70/1.08  Preprocessing        : 0.26
% 1.70/1.08  Parsing              : 0.13
% 1.70/1.08  CNF conversion       : 0.02
% 1.70/1.08  Main loop            : 0.11
% 1.70/1.08  Inferencing          : 0.05
% 1.70/1.08  Reduction            : 0.03
% 1.70/1.08  Demodulation         : 0.02
% 1.70/1.08  BG Simplification    : 0.01
% 1.70/1.08  Subsumption          : 0.02
% 1.70/1.08  Abstraction          : 0.01
% 1.70/1.08  MUC search           : 0.00
% 1.70/1.08  Cooper               : 0.00
% 1.70/1.08  Total                : 0.39
% 1.70/1.08  Index Insertion      : 0.00
% 1.70/1.08  Index Deletion       : 0.00
% 1.70/1.08  Index Matching       : 0.00
% 1.70/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
