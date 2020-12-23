%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:44 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  33 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [D_22,B_23] : r2_hidden(D_22,k2_tarski(D_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_60])).

tff(c_50,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_210,plain,(
    ! [D_63,B_64,A_65,B_66] :
      ( r2_hidden(D_63,B_64)
      | ~ r1_tarski(k2_xboole_0(A_65,B_66),B_64)
      | ~ r2_hidden(D_63,A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_218,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,'#skF_7')
      | ~ r2_hidden(D_67,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_50,c_210])).

tff(c_226,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_63,c_218])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.90/1.20  tff('#skF_7', type, '#skF_7': $i).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.90/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.20  
% 1.90/1.21  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.90/1.21  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.21  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.90/1.21  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.90/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.90/1.21  tff(c_48, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_44, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.21  tff(c_60, plain, (![D_22, B_23]: (r2_hidden(D_22, k2_tarski(D_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.21  tff(c_63, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_60])).
% 1.90/1.21  tff(c_50, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.21  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.21  tff(c_99, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.21  tff(c_210, plain, (![D_63, B_64, A_65, B_66]: (r2_hidden(D_63, B_64) | ~r1_tarski(k2_xboole_0(A_65, B_66), B_64) | ~r2_hidden(D_63, A_65))), inference(resolution, [status(thm)], [c_12, c_99])).
% 1.90/1.21  tff(c_218, plain, (![D_67]: (r2_hidden(D_67, '#skF_7') | ~r2_hidden(D_67, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_50, c_210])).
% 1.90/1.21  tff(c_226, plain, (r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_63, c_218])).
% 1.90/1.21  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_226])).
% 1.90/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  Inference rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Ref     : 0
% 1.90/1.21  #Sup     : 38
% 1.90/1.21  #Fact    : 0
% 1.90/1.21  #Define  : 0
% 1.90/1.21  #Split   : 0
% 1.90/1.21  #Chain   : 0
% 1.90/1.21  #Close   : 0
% 1.90/1.21  
% 1.90/1.21  Ordering : KBO
% 1.90/1.21  
% 1.90/1.21  Simplification rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Subsume      : 3
% 1.90/1.21  #Demod        : 5
% 1.90/1.21  #Tautology    : 17
% 1.90/1.21  #SimpNegUnit  : 1
% 1.90/1.21  #BackRed      : 0
% 1.90/1.21  
% 1.90/1.21  #Partial instantiations: 0
% 1.90/1.21  #Strategies tried      : 1
% 1.90/1.21  
% 1.90/1.21  Timing (in seconds)
% 1.90/1.21  ----------------------
% 1.90/1.21  Preprocessing        : 0.29
% 1.90/1.21  Parsing              : 0.14
% 1.90/1.21  CNF conversion       : 0.02
% 1.90/1.21  Main loop            : 0.17
% 1.90/1.21  Inferencing          : 0.06
% 1.90/1.21  Reduction            : 0.05
% 1.90/1.21  Demodulation         : 0.04
% 1.90/1.21  BG Simplification    : 0.01
% 1.90/1.21  Subsumption          : 0.03
% 1.90/1.21  Abstraction          : 0.01
% 1.90/1.21  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.48
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
