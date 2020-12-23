%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:18 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 116 expanded)
%              Number of equality atoms :   19 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k4_xboole_0(k2_tarski(A,B),C) != k1_xboole_0
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(A)
          & k4_xboole_0(k2_tarski(A,B),C) != k1_tarski(B)
          & k4_xboole_0(k2_tarski(A,B),C) != k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_321,plain,(
    ! [B_84,C_85,A_86] :
      ( ~ r2_hidden(B_84,C_85)
      | k4_xboole_0(k2_tarski(A_86,B_84),C_85) = k1_tarski(A_86)
      | r2_hidden(A_86,C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_38,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_376,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_38])).

tff(c_378,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_393,plain,(
    ! [A_90,B_91,C_92] :
      ( k4_xboole_0(k2_tarski(A_90,B_91),C_92) = k2_tarski(A_90,B_91)
      | r2_hidden(B_91,C_92)
      | r2_hidden(A_90,C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_429,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_34])).

tff(c_459,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_429])).

tff(c_8,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_570,plain,(
    ! [B_99,C_100,A_101] :
      ( ~ r2_hidden(B_99,C_100)
      | k4_xboole_0(k2_tarski(B_99,A_101),C_100) = k1_tarski(A_101)
      | r2_hidden(A_101,C_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_321])).

tff(c_36,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_618,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_36])).

tff(c_655,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_618])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_655])).

tff(c_658,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_659,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_236,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(k2_tarski(A_66,B_67),C_68)
      | ~ r2_hidden(B_67,C_68)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_766,plain,(
    ! [A_111,B_112,C_113] :
      ( k4_xboole_0(k2_tarski(A_111,B_112),C_113) = k1_xboole_0
      | ~ r2_hidden(B_112,C_113)
      | ~ r2_hidden(A_111,C_113) ) ),
    inference(resolution,[status(thm)],[c_236,c_4])).

tff(c_40,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_817,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_40])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_659,c_817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.40  
% 2.59/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.41  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.41  
% 2.59/1.41  %Foreground sorts:
% 2.59/1.41  
% 2.59/1.41  
% 2.59/1.41  %Background operators:
% 2.59/1.41  
% 2.59/1.41  
% 2.59/1.41  %Foreground operators:
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.41  
% 2.59/1.42  tff(f_46, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.59/1.42  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(((~(k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(B))) & ~(k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 2.59/1.42  tff(f_60, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.59/1.42  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.59/1.42  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.59/1.42  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.59/1.42  tff(c_321, plain, (![B_84, C_85, A_86]: (~r2_hidden(B_84, C_85) | k4_xboole_0(k2_tarski(A_86, B_84), C_85)=k1_tarski(A_86) | r2_hidden(A_86, C_85))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.42  tff(c_38, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.42  tff(c_376, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_321, c_38])).
% 2.59/1.42  tff(c_378, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_376])).
% 2.59/1.42  tff(c_393, plain, (![A_90, B_91, C_92]: (k4_xboole_0(k2_tarski(A_90, B_91), C_92)=k2_tarski(A_90, B_91) | r2_hidden(B_91, C_92) | r2_hidden(A_90, C_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.59/1.42  tff(c_34, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.42  tff(c_429, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_393, c_34])).
% 2.59/1.42  tff(c_459, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_378, c_429])).
% 2.59/1.42  tff(c_8, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.59/1.42  tff(c_570, plain, (![B_99, C_100, A_101]: (~r2_hidden(B_99, C_100) | k4_xboole_0(k2_tarski(B_99, A_101), C_100)=k1_tarski(A_101) | r2_hidden(A_101, C_100))), inference(superposition, [status(thm), theory('equality')], [c_8, c_321])).
% 2.59/1.42  tff(c_36, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.42  tff(c_618, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_570, c_36])).
% 2.59/1.42  tff(c_655, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_618])).
% 2.59/1.42  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_655])).
% 2.59/1.42  tff(c_658, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_376])).
% 2.59/1.42  tff(c_659, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_376])).
% 2.59/1.42  tff(c_236, plain, (![A_66, B_67, C_68]: (r1_tarski(k2_tarski(A_66, B_67), C_68) | ~r2_hidden(B_67, C_68) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.59/1.42  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.42  tff(c_766, plain, (![A_111, B_112, C_113]: (k4_xboole_0(k2_tarski(A_111, B_112), C_113)=k1_xboole_0 | ~r2_hidden(B_112, C_113) | ~r2_hidden(A_111, C_113))), inference(resolution, [status(thm)], [c_236, c_4])).
% 2.59/1.42  tff(c_40, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.59/1.42  tff(c_817, plain, (~r2_hidden('#skF_2', '#skF_3') | ~r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_766, c_40])).
% 2.59/1.42  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_658, c_659, c_817])).
% 2.59/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.42  
% 2.59/1.42  Inference rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Ref     : 0
% 2.59/1.42  #Sup     : 214
% 2.59/1.42  #Fact    : 2
% 2.59/1.42  #Define  : 0
% 2.59/1.42  #Split   : 1
% 2.59/1.42  #Chain   : 0
% 2.59/1.42  #Close   : 0
% 2.59/1.42  
% 2.59/1.42  Ordering : KBO
% 2.59/1.42  
% 2.59/1.42  Simplification rules
% 2.59/1.42  ----------------------
% 2.59/1.42  #Subsume      : 69
% 2.59/1.42  #Demod        : 37
% 2.59/1.42  #Tautology    : 86
% 2.59/1.42  #SimpNegUnit  : 10
% 2.59/1.42  #BackRed      : 0
% 2.59/1.42  
% 2.59/1.42  #Partial instantiations: 0
% 2.59/1.42  #Strategies tried      : 1
% 2.59/1.42  
% 2.59/1.42  Timing (in seconds)
% 2.59/1.42  ----------------------
% 2.59/1.42  Preprocessing        : 0.28
% 2.59/1.42  Parsing              : 0.14
% 2.59/1.42  CNF conversion       : 0.02
% 2.59/1.42  Main loop            : 0.32
% 2.59/1.42  Inferencing          : 0.12
% 2.59/1.42  Reduction            : 0.10
% 2.59/1.42  Demodulation         : 0.07
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.06
% 2.59/1.42  Abstraction          : 0.02
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.63
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
