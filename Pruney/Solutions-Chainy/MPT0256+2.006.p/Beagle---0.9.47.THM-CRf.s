%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:02 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   30 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  42 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_54,axiom,(
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
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_193,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [E_27,B_22,C_23] : r2_hidden(E_27,k1_enumset1(E_27,B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_211,plain,(
    ! [A_82,B_83] : r2_hidden(A_82,k2_tarski(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_38])).

tff(c_214,plain,(
    ! [A_28] : r2_hidden(A_28,k1_tarski(A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_211])).

tff(c_1371,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden(A_139,B_140)
      | ~ r2_hidden(A_139,C_141)
      | r2_hidden(A_139,k5_xboole_0(B_140,C_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_151,plain,(
    ! [A_74,B_75] : r1_xboole_0(k3_xboole_0(A_74,B_75),k5_xboole_0(A_74,B_75)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_154,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),k5_xboole_0('#skF_4',k1_tarski('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_151])).

tff(c_255,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_265,plain,(
    ! [C_98] :
      ( ~ r2_hidden(C_98,k5_xboole_0('#skF_4',k1_tarski('#skF_5')))
      | ~ r2_hidden(C_98,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_154,c_255])).

tff(c_1556,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,'#skF_4')
      | ~ r2_hidden(A_149,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1371,c_265])).

tff(c_1568,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_214,c_1556])).

tff(c_1574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:13:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.62  
% 3.16/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.62  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.16/1.62  
% 3.16/1.62  %Foreground sorts:
% 3.16/1.62  
% 3.16/1.62  
% 3.16/1.62  %Background operators:
% 3.16/1.62  
% 3.16/1.62  
% 3.16/1.62  %Foreground operators:
% 3.16/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.16/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.16/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.62  
% 3.58/1.63  tff(f_100, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 3.58/1.63  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.58/1.63  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.58/1.63  tff(f_77, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.58/1.63  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.58/1.63  tff(f_56, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.58/1.63  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.58/1.63  tff(c_74, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.58/1.63  tff(c_56, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.58/1.63  tff(c_193, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.58/1.63  tff(c_38, plain, (![E_27, B_22, C_23]: (r2_hidden(E_27, k1_enumset1(E_27, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.58/1.63  tff(c_211, plain, (![A_82, B_83]: (r2_hidden(A_82, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_38])).
% 3.58/1.63  tff(c_214, plain, (![A_28]: (r2_hidden(A_28, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_211])).
% 3.58/1.63  tff(c_1371, plain, (![A_139, B_140, C_141]: (r2_hidden(A_139, B_140) | ~r2_hidden(A_139, C_141) | r2_hidden(A_139, k5_xboole_0(B_140, C_141)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.58/1.63  tff(c_76, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.58/1.63  tff(c_151, plain, (![A_74, B_75]: (r1_xboole_0(k3_xboole_0(A_74, B_75), k5_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.58/1.63  tff(c_154, plain, (r1_xboole_0(k1_tarski('#skF_5'), k5_xboole_0('#skF_4', k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_76, c_151])).
% 3.58/1.63  tff(c_255, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.58/1.63  tff(c_265, plain, (![C_98]: (~r2_hidden(C_98, k5_xboole_0('#skF_4', k1_tarski('#skF_5'))) | ~r2_hidden(C_98, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_154, c_255])).
% 3.58/1.63  tff(c_1556, plain, (![A_149]: (r2_hidden(A_149, '#skF_4') | ~r2_hidden(A_149, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_1371, c_265])).
% 3.58/1.63  tff(c_1568, plain, (r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_214, c_1556])).
% 3.58/1.63  tff(c_1574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1568])).
% 3.58/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.63  
% 3.58/1.63  Inference rules
% 3.58/1.63  ----------------------
% 3.58/1.63  #Ref     : 0
% 3.58/1.63  #Sup     : 377
% 3.58/1.63  #Fact    : 0
% 3.58/1.63  #Define  : 0
% 3.58/1.63  #Split   : 0
% 3.58/1.63  #Chain   : 0
% 3.58/1.63  #Close   : 0
% 3.58/1.63  
% 3.58/1.63  Ordering : KBO
% 3.58/1.63  
% 3.58/1.63  Simplification rules
% 3.58/1.63  ----------------------
% 3.58/1.63  #Subsume      : 14
% 3.58/1.63  #Demod        : 188
% 3.58/1.63  #Tautology    : 209
% 3.58/1.63  #SimpNegUnit  : 1
% 3.58/1.63  #BackRed      : 3
% 3.58/1.63  
% 3.58/1.63  #Partial instantiations: 0
% 3.58/1.63  #Strategies tried      : 1
% 3.58/1.63  
% 3.58/1.63  Timing (in seconds)
% 3.58/1.63  ----------------------
% 3.58/1.63  Preprocessing        : 0.37
% 3.58/1.63  Parsing              : 0.19
% 3.58/1.63  CNF conversion       : 0.03
% 3.58/1.63  Main loop            : 0.45
% 3.58/1.63  Inferencing          : 0.14
% 3.58/1.63  Reduction            : 0.18
% 3.58/1.63  Demodulation         : 0.15
% 3.58/1.63  BG Simplification    : 0.03
% 3.58/1.63  Subsumption          : 0.07
% 3.58/1.64  Abstraction          : 0.02
% 3.58/1.64  MUC search           : 0.00
% 3.58/1.64  Cooper               : 0.00
% 3.58/1.64  Total                : 0.84
% 3.58/1.64  Index Insertion      : 0.00
% 3.58/1.64  Index Deletion       : 0.00
% 3.58/1.64  Index Matching       : 0.00
% 3.58/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
