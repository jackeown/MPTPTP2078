%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:05 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(k3_xboole_0(A_63,C_64),B_65)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [A_77,B_78,B_79] :
      ( r1_tarski(k3_xboole_0(A_77,B_78),B_79)
      | ~ r1_tarski(B_78,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_266,plain,(
    ! [A_80,B_81,B_82] :
      ( r1_tarski(A_80,B_81)
      | ~ r1_tarski(k2_xboole_0(A_80,B_82),B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_246])).

tff(c_274,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_266])).

tff(c_30,plain,(
    ! [A_42,C_44,B_43] :
      ( r2_hidden(A_42,C_44)
      | ~ r1_tarski(k2_tarski(A_42,B_43),C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_278,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_274,c_30])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.00/1.25  
% 2.00/1.25  %Foreground sorts:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Background operators:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Foreground operators:
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.25  
% 2.00/1.26  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.00/1.26  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.00/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.00/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.00/1.26  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.00/1.26  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.00/1.26  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.26  tff(c_34, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.26  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.26  tff(c_69, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.26  tff(c_73, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(resolution, [status(thm)], [c_8, c_69])).
% 2.00/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.26  tff(c_128, plain, (![A_63, C_64, B_65]: (r1_tarski(k3_xboole_0(A_63, C_64), B_65) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.26  tff(c_246, plain, (![A_77, B_78, B_79]: (r1_tarski(k3_xboole_0(A_77, B_78), B_79) | ~r1_tarski(B_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 2.00/1.26  tff(c_266, plain, (![A_80, B_81, B_82]: (r1_tarski(A_80, B_81) | ~r1_tarski(k2_xboole_0(A_80, B_82), B_81))), inference(superposition, [status(thm), theory('equality')], [c_73, c_246])).
% 2.00/1.26  tff(c_274, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_34, c_266])).
% 2.00/1.26  tff(c_30, plain, (![A_42, C_44, B_43]: (r2_hidden(A_42, C_44) | ~r1_tarski(k2_tarski(A_42, B_43), C_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.26  tff(c_278, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_274, c_30])).
% 2.00/1.26  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_278])).
% 2.00/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  Inference rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Ref     : 0
% 2.00/1.26  #Sup     : 63
% 2.00/1.26  #Fact    : 0
% 2.00/1.26  #Define  : 0
% 2.00/1.26  #Split   : 0
% 2.00/1.26  #Chain   : 0
% 2.00/1.26  #Close   : 0
% 2.00/1.26  
% 2.00/1.26  Ordering : KBO
% 2.00/1.26  
% 2.00/1.26  Simplification rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Subsume      : 3
% 2.00/1.26  #Demod        : 7
% 2.00/1.26  #Tautology    : 40
% 2.00/1.26  #SimpNegUnit  : 1
% 2.00/1.26  #BackRed      : 0
% 2.00/1.26  
% 2.00/1.26  #Partial instantiations: 0
% 2.00/1.26  #Strategies tried      : 1
% 2.00/1.26  
% 2.00/1.26  Timing (in seconds)
% 2.00/1.26  ----------------------
% 2.00/1.26  Preprocessing        : 0.31
% 2.00/1.26  Parsing              : 0.16
% 2.00/1.26  CNF conversion       : 0.02
% 2.00/1.26  Main loop            : 0.20
% 2.00/1.26  Inferencing          : 0.08
% 2.00/1.26  Reduction            : 0.07
% 2.00/1.26  Demodulation         : 0.05
% 2.00/1.26  BG Simplification    : 0.01
% 2.00/1.26  Subsumption          : 0.03
% 2.00/1.26  Abstraction          : 0.01
% 2.00/1.27  MUC search           : 0.00
% 2.00/1.27  Cooper               : 0.00
% 2.00/1.27  Total                : 0.53
% 2.00/1.27  Index Insertion      : 0.00
% 2.00/1.27  Index Deletion       : 0.00
% 2.00/1.27  Index Matching       : 0.00
% 2.00/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
