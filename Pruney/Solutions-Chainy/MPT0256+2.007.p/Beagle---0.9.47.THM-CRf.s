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
% DateTime   : Thu Dec  3 09:52:03 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   49 (  50 expanded)
%              Number of leaves         :   32 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  47 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_76,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_58,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_154,plain,(
    ! [A_78,B_79] : k1_enumset1(A_78,A_78,B_79) = k2_tarski(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [E_29,B_24,C_25] : r2_hidden(E_29,k1_enumset1(E_29,B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    ! [A_80,B_81] : r2_hidden(A_80,k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_40])).

tff(c_175,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_172])).

tff(c_78,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_205,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_214,plain,(
    k5_xboole_0('#skF_4',k1_tarski('#skF_5')) = k4_xboole_0('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_205])).

tff(c_2372,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden(A_159,B_160)
      | ~ r2_hidden(A_159,C_161)
      | r2_hidden(A_159,k5_xboole_0(B_160,C_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2887,plain,(
    ! [A_171] :
      ( r2_hidden(A_171,'#skF_4')
      | ~ r2_hidden(A_171,k1_tarski('#skF_5'))
      | r2_hidden(A_171,k4_xboole_0('#skF_4',k1_tarski('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2372])).

tff(c_26,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_247,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,B_100)
      | ~ r2_hidden(C_101,A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_253,plain,(
    ! [C_101,B_16,A_15] :
      ( ~ r2_hidden(C_101,B_16)
      | ~ r2_hidden(C_101,k4_xboole_0(A_15,B_16)) ) ),
    inference(resolution,[status(thm)],[c_26,c_247])).

tff(c_2892,plain,(
    ! [A_172] :
      ( r2_hidden(A_172,'#skF_4')
      | ~ r2_hidden(A_172,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_2887,c_253])).

tff(c_2904,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_2892])).

tff(c_2910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.80  
% 4.39/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.80  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.39/1.80  
% 4.39/1.80  %Foreground sorts:
% 4.39/1.80  
% 4.39/1.80  
% 4.39/1.80  %Background operators:
% 4.39/1.80  
% 4.39/1.80  
% 4.39/1.80  %Foreground operators:
% 4.39/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.39/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.39/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.39/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.39/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.39/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.39/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.39/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.39/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.39/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.39/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.39/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.39/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.39/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.39/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.39/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.39/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.39/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.39/1.80  
% 4.51/1.82  tff(f_102, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 4.51/1.82  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.51/1.82  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.51/1.82  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.51/1.82  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.51/1.82  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.51/1.82  tff(f_58, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.51/1.82  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.51/1.82  tff(c_76, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.82  tff(c_58, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.51/1.82  tff(c_154, plain, (![A_78, B_79]: (k1_enumset1(A_78, A_78, B_79)=k2_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.51/1.82  tff(c_40, plain, (![E_29, B_24, C_25]: (r2_hidden(E_29, k1_enumset1(E_29, B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.51/1.82  tff(c_172, plain, (![A_80, B_81]: (r2_hidden(A_80, k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_154, c_40])).
% 4.51/1.82  tff(c_175, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_172])).
% 4.51/1.82  tff(c_78, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.51/1.82  tff(c_205, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.82  tff(c_214, plain, (k5_xboole_0('#skF_4', k1_tarski('#skF_5'))=k4_xboole_0('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_205])).
% 4.51/1.82  tff(c_2372, plain, (![A_159, B_160, C_161]: (r2_hidden(A_159, B_160) | ~r2_hidden(A_159, C_161) | r2_hidden(A_159, k5_xboole_0(B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.82  tff(c_2887, plain, (![A_171]: (r2_hidden(A_171, '#skF_4') | ~r2_hidden(A_171, k1_tarski('#skF_5')) | r2_hidden(A_171, k4_xboole_0('#skF_4', k1_tarski('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_214, c_2372])).
% 4.51/1.82  tff(c_26, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.82  tff(c_247, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, B_100) | ~r2_hidden(C_101, A_99))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.82  tff(c_253, plain, (![C_101, B_16, A_15]: (~r2_hidden(C_101, B_16) | ~r2_hidden(C_101, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_26, c_247])).
% 4.51/1.82  tff(c_2892, plain, (![A_172]: (r2_hidden(A_172, '#skF_4') | ~r2_hidden(A_172, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_2887, c_253])).
% 4.51/1.82  tff(c_2904, plain, (r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_175, c_2892])).
% 4.51/1.82  tff(c_2910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2904])).
% 4.51/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.82  
% 4.51/1.82  Inference rules
% 4.51/1.82  ----------------------
% 4.51/1.82  #Ref     : 0
% 4.51/1.82  #Sup     : 739
% 4.51/1.82  #Fact    : 0
% 4.51/1.82  #Define  : 0
% 4.51/1.82  #Split   : 0
% 4.51/1.82  #Chain   : 0
% 4.51/1.82  #Close   : 0
% 4.51/1.82  
% 4.51/1.82  Ordering : KBO
% 4.51/1.82  
% 4.51/1.82  Simplification rules
% 4.51/1.82  ----------------------
% 4.51/1.82  #Subsume      : 32
% 4.51/1.82  #Demod        : 370
% 4.51/1.82  #Tautology    : 377
% 4.51/1.82  #SimpNegUnit  : 8
% 4.51/1.82  #BackRed      : 2
% 4.51/1.82  
% 4.51/1.82  #Partial instantiations: 0
% 4.51/1.82  #Strategies tried      : 1
% 4.51/1.82  
% 4.51/1.82  Timing (in seconds)
% 4.51/1.82  ----------------------
% 4.51/1.82  Preprocessing        : 0.36
% 4.51/1.82  Parsing              : 0.18
% 4.51/1.82  CNF conversion       : 0.03
% 4.51/1.82  Main loop            : 0.69
% 4.51/1.82  Inferencing          : 0.22
% 4.51/1.82  Reduction            : 0.29
% 4.51/1.82  Demodulation         : 0.24
% 4.51/1.82  BG Simplification    : 0.03
% 4.51/1.82  Subsumption          : 0.10
% 4.51/1.82  Abstraction          : 0.04
% 4.51/1.82  MUC search           : 0.00
% 4.51/1.82  Cooper               : 0.00
% 4.51/1.82  Total                : 1.08
% 4.51/1.82  Index Insertion      : 0.00
% 4.51/1.83  Index Deletion       : 0.00
% 4.51/1.83  Index Matching       : 0.00
% 4.51/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
