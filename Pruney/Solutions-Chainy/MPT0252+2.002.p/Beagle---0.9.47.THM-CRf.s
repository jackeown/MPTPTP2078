%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:01 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   50 (  52 expanded)
%              Number of leaves         :   31 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   42 (  45 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_112,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_93,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_118,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_94,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_170,plain,(
    ! [A_68,B_69] : k1_enumset1(A_68,A_68,B_69) = k2_tarski(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_66,plain,(
    ! [E_38,A_32,C_34] : r2_hidden(E_38,k1_enumset1(A_32,E_38,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_176,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_66])).

tff(c_58,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_206,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_269,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(B_82,A_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_206])).

tff(c_92,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_275,plain,(
    ! [B_82,A_81] : k2_xboole_0(B_82,A_81) = k2_xboole_0(A_81,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_92])).

tff(c_96,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_293,plain,(
    r1_tarski(k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_96])).

tff(c_428,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_430,plain,
    ( k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')) = '#skF_8'
    | ~ r1_tarski('#skF_8',k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_293,c_428])).

tff(c_439,plain,(
    k2_xboole_0('#skF_8',k2_tarski('#skF_6','#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_430])).

tff(c_495,plain,(
    ! [D_108,B_109,A_110] :
      ( ~ r2_hidden(D_108,B_109)
      | r2_hidden(D_108,k2_xboole_0(A_110,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_701,plain,(
    ! [D_129] :
      ( ~ r2_hidden(D_129,k2_tarski('#skF_6','#skF_7'))
      | r2_hidden(D_129,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_495])).

tff(c_717,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_176,c_701])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5
% 2.58/1.37  
% 2.58/1.37  %Foreground sorts:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Background operators:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Foreground operators:
% 2.58/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.58/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.58/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.58/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.58/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.37  
% 2.58/1.38  tff(f_123, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.58/1.38  tff(f_112, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.58/1.38  tff(f_110, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.58/1.38  tff(f_93, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.58/1.38  tff(f_95, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.58/1.38  tff(f_118, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.58/1.38  tff(f_67, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.38  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.58/1.38  tff(c_94, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.58/1.38  tff(c_170, plain, (![A_68, B_69]: (k1_enumset1(A_68, A_68, B_69)=k2_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.58/1.38  tff(c_66, plain, (![E_38, A_32, C_34]: (r2_hidden(E_38, k1_enumset1(A_32, E_38, C_34)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.58/1.38  tff(c_176, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_66])).
% 2.58/1.38  tff(c_58, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.38  tff(c_60, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.58/1.38  tff(c_206, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.58/1.38  tff(c_269, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(B_82, A_81))), inference(superposition, [status(thm), theory('equality')], [c_60, c_206])).
% 2.58/1.38  tff(c_92, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.58/1.38  tff(c_275, plain, (![B_82, A_81]: (k2_xboole_0(B_82, A_81)=k2_xboole_0(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_269, c_92])).
% 2.58/1.38  tff(c_96, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.58/1.38  tff(c_293, plain, (r1_tarski(k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7')), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_96])).
% 2.58/1.38  tff(c_428, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.38  tff(c_430, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7'))='#skF_8' | ~r1_tarski('#skF_8', k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_293, c_428])).
% 2.58/1.38  tff(c_439, plain, (k2_xboole_0('#skF_8', k2_tarski('#skF_6', '#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_430])).
% 2.58/1.38  tff(c_495, plain, (![D_108, B_109, A_110]: (~r2_hidden(D_108, B_109) | r2_hidden(D_108, k2_xboole_0(A_110, B_109)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.58/1.38  tff(c_701, plain, (![D_129]: (~r2_hidden(D_129, k2_tarski('#skF_6', '#skF_7')) | r2_hidden(D_129, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_439, c_495])).
% 2.58/1.38  tff(c_717, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_176, c_701])).
% 2.58/1.38  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_717])).
% 2.58/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  Inference rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Ref     : 0
% 2.58/1.38  #Sup     : 150
% 2.58/1.38  #Fact    : 0
% 2.58/1.38  #Define  : 0
% 2.58/1.38  #Split   : 0
% 2.58/1.38  #Chain   : 0
% 2.58/1.38  #Close   : 0
% 2.58/1.38  
% 2.58/1.38  Ordering : KBO
% 2.58/1.38  
% 2.58/1.38  Simplification rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Subsume      : 9
% 2.58/1.38  #Demod        : 57
% 2.58/1.38  #Tautology    : 105
% 2.58/1.38  #SimpNegUnit  : 1
% 2.58/1.38  #BackRed      : 3
% 2.58/1.38  
% 2.58/1.38  #Partial instantiations: 0
% 2.58/1.38  #Strategies tried      : 1
% 2.58/1.38  
% 2.58/1.38  Timing (in seconds)
% 2.58/1.38  ----------------------
% 2.58/1.38  Preprocessing        : 0.34
% 2.58/1.38  Parsing              : 0.17
% 2.58/1.38  CNF conversion       : 0.03
% 2.58/1.38  Main loop            : 0.29
% 2.58/1.38  Inferencing          : 0.09
% 2.58/1.39  Reduction            : 0.11
% 2.58/1.39  Demodulation         : 0.08
% 2.58/1.39  BG Simplification    : 0.02
% 2.58/1.39  Subsumption          : 0.06
% 2.58/1.39  Abstraction          : 0.02
% 2.58/1.39  MUC search           : 0.00
% 2.58/1.39  Cooper               : 0.00
% 2.58/1.39  Total                : 0.65
% 2.58/1.39  Index Insertion      : 0.00
% 2.58/1.39  Index Deletion       : 0.00
% 2.58/1.39  Index Matching       : 0.00
% 2.58/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
