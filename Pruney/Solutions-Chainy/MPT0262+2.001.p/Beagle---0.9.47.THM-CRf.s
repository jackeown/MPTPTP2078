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
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 ( 104 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

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

tff(c_44,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    ! [E_69,C_70,B_71,A_72] :
      ( E_69 = C_70
      | E_69 = B_71
      | E_69 = A_72
      | ~ r2_hidden(E_69,k1_enumset1(A_72,B_71,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_123,plain,(
    ! [E_73,B_74,A_75] :
      ( E_73 = B_74
      | E_73 = A_75
      | E_73 = A_75
      | ~ r2_hidden(E_73,k2_tarski(A_75,B_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_94])).

tff(c_175,plain,(
    ! [A_97,B_98,B_99] :
      ( '#skF_1'(k2_tarski(A_97,B_98),B_99) = B_98
      | '#skF_1'(k2_tarski(A_97,B_98),B_99) = A_97
      | r1_xboole_0(k2_tarski(A_97,B_98),B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_182,plain,
    ( '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_175,c_44])).

tff(c_183,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_190,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_4])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_48,c_190])).

tff(c_197,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_6'),'#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_205,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | r1_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_4])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_46,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:28:12 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.06/1.23  
% 2.06/1.23  %Foreground sorts:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Background operators:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Foreground operators:
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.06/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.06/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.23  
% 2.06/1.23  tff(f_81, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.06/1.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.23  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.23  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.06/1.23  tff(c_44, plain, (~r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.23  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.23  tff(c_48, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.06/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.23  tff(c_32, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.23  tff(c_94, plain, (![E_69, C_70, B_71, A_72]: (E_69=C_70 | E_69=B_71 | E_69=A_72 | ~r2_hidden(E_69, k1_enumset1(A_72, B_71, C_70)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.23  tff(c_123, plain, (![E_73, B_74, A_75]: (E_73=B_74 | E_73=A_75 | E_73=A_75 | ~r2_hidden(E_73, k2_tarski(A_75, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_94])).
% 2.06/1.23  tff(c_175, plain, (![A_97, B_98, B_99]: ('#skF_1'(k2_tarski(A_97, B_98), B_99)=B_98 | '#skF_1'(k2_tarski(A_97, B_98), B_99)=A_97 | r1_xboole_0(k2_tarski(A_97, B_98), B_99))), inference(resolution, [status(thm)], [c_6, c_123])).
% 2.06/1.23  tff(c_182, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_6' | '#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_175, c_44])).
% 2.06/1.23  tff(c_183, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_182])).
% 2.06/1.23  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.23  tff(c_190, plain, (r2_hidden('#skF_4', '#skF_5') | r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_183, c_4])).
% 2.06/1.23  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_48, c_190])).
% 2.06/1.23  tff(c_197, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_6'), '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_182])).
% 2.06/1.23  tff(c_205, plain, (r2_hidden('#skF_6', '#skF_5') | r1_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_197, c_4])).
% 2.06/1.23  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_46, c_205])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 36
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 1
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 0
% 2.06/1.24  #Demod        : 3
% 2.06/1.24  #Tautology    : 22
% 2.06/1.24  #SimpNegUnit  : 4
% 2.06/1.24  #BackRed      : 0
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.32
% 2.06/1.24  Parsing              : 0.16
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.17
% 2.06/1.24  Inferencing          : 0.06
% 2.06/1.24  Reduction            : 0.05
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.02
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.02
% 2.06/1.24  MUC search           : 0.00
% 2.06/1.24  Cooper               : 0.00
% 2.06/1.24  Total                : 0.51
% 2.06/1.24  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
