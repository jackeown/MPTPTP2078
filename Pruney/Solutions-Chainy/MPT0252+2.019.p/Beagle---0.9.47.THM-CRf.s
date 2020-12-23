%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:03 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  33 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_492,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_500,plain,
    ( k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_37,c_492])).

tff(c_510,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_500])).

tff(c_68,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [B_35,A_36] : r1_tarski(B_35,k2_xboole_0(A_36,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_24])).

tff(c_406,plain,(
    ! [A_63,C_64,B_65] :
      ( r2_hidden(A_63,C_64)
      | ~ r1_tarski(k2_tarski(A_63,B_65),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_424,plain,(
    ! [A_63,A_36,B_65] : r2_hidden(A_63,k2_xboole_0(A_36,k2_tarski(A_63,B_65))) ),
    inference(resolution,[status(thm)],[c_92,c_406])).

tff(c_525,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_424])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.33  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.17/1.33  
% 2.17/1.33  %Foreground sorts:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Background operators:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Foreground operators:
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.33  
% 2.17/1.34  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.17/1.34  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.17/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.17/1.34  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.34  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.17/1.34  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.34  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.17/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.34  tff(c_34, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.34  tff(c_37, plain, (r1_tarski(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 2.17/1.34  tff(c_492, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.34  tff(c_500, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_37, c_492])).
% 2.17/1.34  tff(c_510, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_500])).
% 2.17/1.34  tff(c_68, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.34  tff(c_92, plain, (![B_35, A_36]: (r1_tarski(B_35, k2_xboole_0(A_36, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_24])).
% 2.17/1.34  tff(c_406, plain, (![A_63, C_64, B_65]: (r2_hidden(A_63, C_64) | ~r1_tarski(k2_tarski(A_63, B_65), C_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.34  tff(c_424, plain, (![A_63, A_36, B_65]: (r2_hidden(A_63, k2_xboole_0(A_36, k2_tarski(A_63, B_65))))), inference(resolution, [status(thm)], [c_92, c_406])).
% 2.17/1.34  tff(c_525, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_510, c_424])).
% 2.17/1.34  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_525])).
% 2.17/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  Inference rules
% 2.17/1.34  ----------------------
% 2.17/1.34  #Ref     : 0
% 2.17/1.34  #Sup     : 123
% 2.17/1.34  #Fact    : 0
% 2.17/1.34  #Define  : 0
% 2.17/1.34  #Split   : 0
% 2.17/1.34  #Chain   : 0
% 2.17/1.34  #Close   : 0
% 2.17/1.34  
% 2.17/1.34  Ordering : KBO
% 2.17/1.34  
% 2.17/1.34  Simplification rules
% 2.17/1.34  ----------------------
% 2.17/1.34  #Subsume      : 0
% 2.17/1.34  #Demod        : 60
% 2.17/1.34  #Tautology    : 84
% 2.17/1.34  #SimpNegUnit  : 1
% 2.17/1.34  #BackRed      : 3
% 2.17/1.34  
% 2.17/1.34  #Partial instantiations: 0
% 2.17/1.34  #Strategies tried      : 1
% 2.17/1.34  
% 2.17/1.34  Timing (in seconds)
% 2.17/1.34  ----------------------
% 2.17/1.34  Preprocessing        : 0.31
% 2.17/1.34  Parsing              : 0.18
% 2.17/1.34  CNF conversion       : 0.02
% 2.17/1.34  Main loop            : 0.24
% 2.17/1.34  Inferencing          : 0.08
% 2.17/1.34  Reduction            : 0.09
% 2.17/1.34  Demodulation         : 0.07
% 2.17/1.34  BG Simplification    : 0.01
% 2.17/1.34  Subsumption          : 0.04
% 2.17/1.34  Abstraction          : 0.01
% 2.17/1.34  MUC search           : 0.00
% 2.17/1.34  Cooper               : 0.00
% 2.17/1.34  Total                : 0.57
% 2.17/1.34  Index Insertion      : 0.00
% 2.17/1.34  Index Deletion       : 0.00
% 2.17/1.34  Index Matching       : 0.00
% 2.17/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
