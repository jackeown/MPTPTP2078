%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:26 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.55s
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
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_74,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_175,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [E_31,A_25,C_27] : r2_hidden(E_31,k1_enumset1(A_25,E_31,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_184,plain,(
    ! [A_77,B_78] : r2_hidden(A_77,k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_40])).

tff(c_1422,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(A_150,B_151)
      | ~ r2_hidden(A_150,C_152)
      | r2_hidden(A_150,k5_xboole_0(B_151,C_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    k3_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_211,plain,(
    ! [A_83,B_84] : r1_xboole_0(k3_xboole_0(A_83,B_84),k5_xboole_0(A_83,B_84)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_211])).

tff(c_227,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_329,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,B_99)
      | ~ r2_hidden(C_100,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_339,plain,(
    ! [C_100] :
      ( ~ r2_hidden(C_100,k5_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')))
      | ~ r2_hidden(C_100,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_227,c_329])).

tff(c_1559,plain,(
    ! [A_154] :
      ( r2_hidden(A_154,'#skF_6')
      | ~ r2_hidden(A_154,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1422,c_339])).

tff(c_1571,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_184,c_1559])).

tff(c_1581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:49:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.42/1.55  
% 3.42/1.55  %Foreground sorts:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Background operators:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Foreground operators:
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.42/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.42/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.42/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.42/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.42/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.42/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.55  
% 3.55/1.56  tff(f_100, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 3.55/1.56  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.55/1.56  tff(f_81, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.55/1.56  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.55/1.56  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.55/1.56  tff(f_58, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.55/1.56  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.55/1.56  tff(c_74, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.55/1.56  tff(c_175, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.55/1.56  tff(c_40, plain, (![E_31, A_25, C_27]: (r2_hidden(E_31, k1_enumset1(A_25, E_31, C_27)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.55/1.56  tff(c_184, plain, (![A_77, B_78]: (r2_hidden(A_77, k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_175, c_40])).
% 3.55/1.56  tff(c_1422, plain, (![A_150, B_151, C_152]: (r2_hidden(A_150, B_151) | ~r2_hidden(A_150, C_152) | r2_hidden(A_150, k5_xboole_0(B_151, C_152)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.55/1.56  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.56  tff(c_76, plain, (k3_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.55/1.56  tff(c_211, plain, (![A_83, B_84]: (r1_xboole_0(k3_xboole_0(A_83, B_84), k5_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.55/1.56  tff(c_214, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_211])).
% 3.55/1.56  tff(c_227, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_214])).
% 3.55/1.56  tff(c_329, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, B_99) | ~r2_hidden(C_100, A_98))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.56  tff(c_339, plain, (![C_100]: (~r2_hidden(C_100, k5_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))) | ~r2_hidden(C_100, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_227, c_329])).
% 3.55/1.56  tff(c_1559, plain, (![A_154]: (r2_hidden(A_154, '#skF_6') | ~r2_hidden(A_154, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_1422, c_339])).
% 3.55/1.56  tff(c_1571, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_184, c_1559])).
% 3.55/1.56  tff(c_1581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1571])).
% 3.55/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  Inference rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Ref     : 0
% 3.55/1.56  #Sup     : 382
% 3.55/1.56  #Fact    : 0
% 3.55/1.56  #Define  : 0
% 3.55/1.56  #Split   : 0
% 3.55/1.56  #Chain   : 0
% 3.55/1.56  #Close   : 0
% 3.55/1.56  
% 3.55/1.56  Ordering : KBO
% 3.55/1.56  
% 3.55/1.56  Simplification rules
% 3.55/1.56  ----------------------
% 3.55/1.56  #Subsume      : 14
% 3.55/1.56  #Demod        : 168
% 3.55/1.56  #Tautology    : 224
% 3.55/1.56  #SimpNegUnit  : 1
% 3.55/1.56  #BackRed      : 0
% 3.55/1.56  
% 3.55/1.56  #Partial instantiations: 0
% 3.55/1.56  #Strategies tried      : 1
% 3.55/1.56  
% 3.55/1.56  Timing (in seconds)
% 3.55/1.56  ----------------------
% 3.55/1.56  Preprocessing        : 0.35
% 3.55/1.56  Parsing              : 0.18
% 3.55/1.56  CNF conversion       : 0.03
% 3.55/1.56  Main loop            : 0.45
% 3.55/1.56  Inferencing          : 0.14
% 3.55/1.56  Reduction            : 0.18
% 3.55/1.56  Demodulation         : 0.15
% 3.55/1.57  BG Simplification    : 0.03
% 3.55/1.57  Subsumption          : 0.07
% 3.55/1.57  Abstraction          : 0.03
% 3.55/1.57  MUC search           : 0.00
% 3.55/1.57  Cooper               : 0.00
% 3.55/1.57  Total                : 0.83
% 3.55/1.57  Index Insertion      : 0.00
% 3.55/1.57  Index Deletion       : 0.00
% 3.55/1.57  Index Matching       : 0.00
% 3.55/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
