%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:29 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   30 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_78,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_155,plain,(
    ! [A_79,B_80] : k1_enumset1(A_79,A_79,B_80) = k2_tarski(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    ! [E_29,A_23,C_25] : r2_hidden(E_29,k1_enumset1(A_23,E_29,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_161,plain,(
    ! [A_79,B_80] : r2_hidden(A_79,k2_tarski(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_38])).

tff(c_1296,plain,(
    ! [A_147,B_148,C_149] :
      ( r2_hidden(A_147,B_148)
      | ~ r2_hidden(A_147,C_149)
      | r2_hidden(A_147,k5_xboole_0(B_148,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_206,plain,(
    ! [A_89,B_90] : r1_xboole_0(k3_xboole_0(A_89,B_90),k5_xboole_0(A_89,B_90)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_209,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_206])).

tff(c_222,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_260,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r1_xboole_0(A_101,B_102)
      | ~ r2_hidden(C_103,B_102)
      | ~ r2_hidden(C_103,A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,(
    ! [C_103] :
      ( ~ r2_hidden(C_103,k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')))
      | ~ r2_hidden(C_103,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_222,c_260])).

tff(c_1342,plain,(
    ! [A_150] :
      ( r2_hidden(A_150,'#skF_6')
      | ~ r2_hidden(A_150,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1296,c_270])).

tff(c_1358,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_161,c_1342])).

tff(c_1365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.64  
% 3.35/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.64  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.35/1.64  
% 3.35/1.64  %Foreground sorts:
% 3.35/1.64  
% 3.35/1.64  
% 3.35/1.64  %Background operators:
% 3.35/1.64  
% 3.35/1.64  
% 3.35/1.64  %Foreground operators:
% 3.35/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.35/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.35/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.35/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.35/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.35/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.35/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.35/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.35/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.64  
% 3.35/1.65  tff(f_104, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.35/1.65  tff(f_89, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.35/1.65  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.35/1.65  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.35/1.65  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.35/1.65  tff(f_58, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.35/1.65  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.35/1.65  tff(c_78, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.35/1.65  tff(c_155, plain, (![A_79, B_80]: (k1_enumset1(A_79, A_79, B_80)=k2_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.35/1.65  tff(c_38, plain, (![E_29, A_23, C_25]: (r2_hidden(E_29, k1_enumset1(A_23, E_29, C_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.35/1.65  tff(c_161, plain, (![A_79, B_80]: (r2_hidden(A_79, k2_tarski(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_38])).
% 3.35/1.65  tff(c_1296, plain, (![A_147, B_148, C_149]: (r2_hidden(A_147, B_148) | ~r2_hidden(A_147, C_149) | r2_hidden(A_147, k5_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.65  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.35/1.65  tff(c_80, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.35/1.65  tff(c_206, plain, (![A_89, B_90]: (r1_xboole_0(k3_xboole_0(A_89, B_90), k5_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.35/1.65  tff(c_209, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_206])).
% 3.35/1.65  tff(c_222, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_209])).
% 3.35/1.65  tff(c_260, plain, (![A_101, B_102, C_103]: (~r1_xboole_0(A_101, B_102) | ~r2_hidden(C_103, B_102) | ~r2_hidden(C_103, A_101))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.65  tff(c_270, plain, (![C_103]: (~r2_hidden(C_103, k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))) | ~r2_hidden(C_103, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_222, c_260])).
% 3.35/1.65  tff(c_1342, plain, (![A_150]: (r2_hidden(A_150, '#skF_6') | ~r2_hidden(A_150, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_1296, c_270])).
% 3.35/1.65  tff(c_1358, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_161, c_1342])).
% 3.35/1.65  tff(c_1365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1358])).
% 3.35/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.65  
% 3.35/1.65  Inference rules
% 3.35/1.65  ----------------------
% 3.35/1.65  #Ref     : 0
% 3.35/1.65  #Sup     : 321
% 3.35/1.65  #Fact    : 0
% 3.35/1.65  #Define  : 0
% 3.35/1.65  #Split   : 0
% 3.35/1.65  #Chain   : 0
% 3.35/1.65  #Close   : 0
% 3.35/1.65  
% 3.35/1.65  Ordering : KBO
% 3.35/1.65  
% 3.35/1.65  Simplification rules
% 3.35/1.65  ----------------------
% 3.35/1.65  #Subsume      : 9
% 3.35/1.65  #Demod        : 148
% 3.35/1.65  #Tautology    : 195
% 3.35/1.65  #SimpNegUnit  : 1
% 3.35/1.65  #BackRed      : 0
% 3.35/1.65  
% 3.35/1.65  #Partial instantiations: 0
% 3.35/1.65  #Strategies tried      : 1
% 3.35/1.65  
% 3.35/1.65  Timing (in seconds)
% 3.35/1.65  ----------------------
% 3.35/1.65  Preprocessing        : 0.36
% 3.35/1.65  Parsing              : 0.19
% 3.35/1.65  CNF conversion       : 0.03
% 3.35/1.65  Main loop            : 0.46
% 3.35/1.65  Inferencing          : 0.14
% 3.35/1.65  Reduction            : 0.18
% 3.35/1.65  Demodulation         : 0.15
% 3.35/1.65  BG Simplification    : 0.03
% 3.35/1.65  Subsumption          : 0.07
% 3.35/1.65  Abstraction          : 0.03
% 3.35/1.65  MUC search           : 0.00
% 3.35/1.65  Cooper               : 0.00
% 3.35/1.65  Total                : 0.85
% 3.35/1.65  Index Insertion      : 0.00
% 3.35/1.65  Index Deletion       : 0.00
% 3.35/1.65  Index Matching       : 0.00
% 3.35/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
