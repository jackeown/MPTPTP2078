%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:40 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_38,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_8,B_9] : k3_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_353,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(k3_xboole_0(A_98,C_99),B_100)
      | ~ r1_tarski(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_376,plain,(
    ! [B_101,A_102,B_103] :
      ( r1_tarski(k3_xboole_0(B_101,A_102),B_103)
      | ~ r1_tarski(A_102,B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_353])).

tff(c_408,plain,(
    ! [A_107,B_108,B_109] :
      ( r1_tarski(A_107,B_108)
      | ~ r1_tarski(k2_xboole_0(A_107,B_109),B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_376])).

tff(c_424,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_408])).

tff(c_18,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [B_75,C_76,A_77] :
      ( r2_hidden(B_75,C_76)
      | ~ r1_tarski(k2_tarski(A_77,B_75),C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_239,plain,(
    ! [A_30,C_76] :
      ( r2_hidden(A_30,C_76)
      | ~ r1_tarski(k1_tarski(A_30),C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_232])).

tff(c_428,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_424,c_239])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:14:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.26/1.34  
% 2.26/1.34  %Foreground sorts:
% 2.26/1.34  
% 2.26/1.34  
% 2.26/1.34  %Background operators:
% 2.26/1.34  
% 2.26/1.34  
% 2.26/1.34  %Foreground operators:
% 2.26/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.34  
% 2.26/1.35  tff(f_70, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.26/1.35  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.26/1.35  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.26/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.26/1.35  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.26/1.35  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.26/1.35  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.26/1.35  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.35  tff(c_40, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.26/1.35  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.35  tff(c_84, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.35  tff(c_92, plain, (![A_8, B_9]: (k3_xboole_0(A_8, k2_xboole_0(A_8, B_9))=A_8)), inference(resolution, [status(thm)], [c_8, c_84])).
% 2.26/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.35  tff(c_353, plain, (![A_98, C_99, B_100]: (r1_tarski(k3_xboole_0(A_98, C_99), B_100) | ~r1_tarski(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.35  tff(c_376, plain, (![B_101, A_102, B_103]: (r1_tarski(k3_xboole_0(B_101, A_102), B_103) | ~r1_tarski(A_102, B_103))), inference(superposition, [status(thm), theory('equality')], [c_2, c_353])).
% 2.26/1.35  tff(c_408, plain, (![A_107, B_108, B_109]: (r1_tarski(A_107, B_108) | ~r1_tarski(k2_xboole_0(A_107, B_109), B_108))), inference(superposition, [status(thm), theory('equality')], [c_92, c_376])).
% 2.26/1.35  tff(c_424, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_40, c_408])).
% 2.26/1.35  tff(c_18, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.35  tff(c_232, plain, (![B_75, C_76, A_77]: (r2_hidden(B_75, C_76) | ~r1_tarski(k2_tarski(A_77, B_75), C_76))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.35  tff(c_239, plain, (![A_30, C_76]: (r2_hidden(A_30, C_76) | ~r1_tarski(k1_tarski(A_30), C_76))), inference(superposition, [status(thm), theory('equality')], [c_18, c_232])).
% 2.26/1.35  tff(c_428, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_424, c_239])).
% 2.26/1.35  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_428])).
% 2.26/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.35  
% 2.26/1.35  Inference rules
% 2.26/1.35  ----------------------
% 2.26/1.35  #Ref     : 0
% 2.26/1.35  #Sup     : 95
% 2.26/1.35  #Fact    : 0
% 2.26/1.35  #Define  : 0
% 2.26/1.35  #Split   : 0
% 2.26/1.35  #Chain   : 0
% 2.26/1.35  #Close   : 0
% 2.26/1.35  
% 2.26/1.35  Ordering : KBO
% 2.26/1.35  
% 2.26/1.35  Simplification rules
% 2.26/1.35  ----------------------
% 2.26/1.35  #Subsume      : 4
% 2.26/1.35  #Demod        : 22
% 2.26/1.35  #Tautology    : 62
% 2.26/1.35  #SimpNegUnit  : 1
% 2.26/1.35  #BackRed      : 0
% 2.26/1.35  
% 2.26/1.35  #Partial instantiations: 0
% 2.26/1.35  #Strategies tried      : 1
% 2.26/1.35  
% 2.26/1.35  Timing (in seconds)
% 2.26/1.35  ----------------------
% 2.26/1.35  Preprocessing        : 0.33
% 2.26/1.35  Parsing              : 0.18
% 2.26/1.35  CNF conversion       : 0.02
% 2.26/1.35  Main loop            : 0.21
% 2.26/1.35  Inferencing          : 0.08
% 2.26/1.35  Reduction            : 0.08
% 2.26/1.35  Demodulation         : 0.06
% 2.26/1.35  BG Simplification    : 0.02
% 2.26/1.35  Subsumption          : 0.03
% 2.26/1.35  Abstraction          : 0.01
% 2.26/1.35  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.57
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
