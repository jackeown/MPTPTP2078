%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:10 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_49,plain,(
    ! [A_24,B_25] : r2_hidden(A_24,k2_tarski(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_12])).

tff(c_36,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_63,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,B_35)
      | ~ r2_hidden(C_36,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_6')
      | ~ r2_hidden(C_37,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_63])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_49,c_67])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 1.66/1.14  
% 1.66/1.14  %Foreground sorts:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Background operators:
% 1.66/1.14  
% 1.66/1.14  
% 1.66/1.14  %Foreground operators:
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.66/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.66/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.66/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.14  
% 1.66/1.15  tff(f_66, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.66/1.15  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.66/1.15  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.66/1.15  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.66/1.15  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.66/1.15  tff(c_40, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.15  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.15  tff(c_49, plain, (![A_24, B_25]: (r2_hidden(A_24, k2_tarski(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_12])).
% 1.66/1.15  tff(c_36, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.66/1.15  tff(c_63, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, B_35) | ~r2_hidden(C_36, A_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.15  tff(c_67, plain, (![C_37]: (~r2_hidden(C_37, '#skF_6') | ~r2_hidden(C_37, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_36, c_63])).
% 1.66/1.15  tff(c_79, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_49, c_67])).
% 1.66/1.15  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_79])).
% 1.66/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  Inference rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Ref     : 0
% 1.66/1.15  #Sup     : 10
% 1.66/1.15  #Fact    : 0
% 1.66/1.15  #Define  : 0
% 1.66/1.15  #Split   : 0
% 1.66/1.15  #Chain   : 0
% 1.66/1.15  #Close   : 0
% 1.66/1.15  
% 1.66/1.15  Ordering : KBO
% 1.66/1.15  
% 1.66/1.15  Simplification rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Subsume      : 0
% 1.66/1.15  #Demod        : 2
% 1.66/1.15  #Tautology    : 3
% 1.66/1.15  #SimpNegUnit  : 0
% 1.66/1.15  #BackRed      : 0
% 1.66/1.15  
% 1.66/1.15  #Partial instantiations: 0
% 1.66/1.15  #Strategies tried      : 1
% 1.66/1.15  
% 1.66/1.15  Timing (in seconds)
% 1.66/1.15  ----------------------
% 1.66/1.16  Preprocessing        : 0.29
% 1.66/1.16  Parsing              : 0.14
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.11
% 1.66/1.16  Inferencing          : 0.03
% 1.66/1.16  Reduction            : 0.03
% 1.66/1.16  Demodulation         : 0.03
% 1.66/1.16  BG Simplification    : 0.01
% 1.66/1.16  Subsumption          : 0.02
% 1.66/1.16  Abstraction          : 0.01
% 1.66/1.16  MUC search           : 0.00
% 1.66/1.16  Cooper               : 0.00
% 1.66/1.16  Total                : 0.42
% 1.66/1.16  Index Insertion      : 0.00
% 1.66/1.16  Index Deletion       : 0.00
% 1.66/1.16  Index Matching       : 0.00
% 1.66/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
