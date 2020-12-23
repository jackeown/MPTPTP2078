%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:32 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_74,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1036,plain,(
    ! [A_145,B_146,C_147] :
      ( r1_tarski(k2_tarski(A_145,B_146),C_147)
      | ~ r2_hidden(B_146,C_147)
      | ~ r2_hidden(A_145,C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1247,plain,(
    ! [A_173,C_174] :
      ( r1_tarski(k1_tarski(A_173),C_174)
      | ~ r2_hidden(A_173,C_174)
      | ~ r2_hidden(A_173,C_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1036])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k2_xboole_0(A_22,B_23) = B_23
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1267,plain,(
    ! [A_175,C_176] :
      ( k2_xboole_0(k1_tarski(A_175),C_176) = C_176
      | ~ r2_hidden(A_175,C_176) ) ),
    inference(resolution,[status(thm)],[c_1247,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1350,plain,(
    ! [C_178,A_179] :
      ( k2_xboole_0(C_178,k1_tarski(A_179)) = C_178
      | ~ r2_hidden(A_179,C_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_2])).

tff(c_42,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_76,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_77,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42,c_76])).

tff(c_1374,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_77])).

tff(c_1405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:19:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.14/1.49  
% 3.14/1.49  %Foreground sorts:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Background operators:
% 3.14/1.49  
% 3.14/1.49  
% 3.14/1.49  %Foreground operators:
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.14/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.14/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.14/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.14/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.14/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.14/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.49  
% 3.14/1.50  tff(f_95, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 3.14/1.50  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.14/1.50  tff(f_90, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.14/1.50  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.14/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.14/1.50  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.14/1.50  tff(c_74, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.50  tff(c_50, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.14/1.50  tff(c_1036, plain, (![A_145, B_146, C_147]: (r1_tarski(k2_tarski(A_145, B_146), C_147) | ~r2_hidden(B_146, C_147) | ~r2_hidden(A_145, C_147))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.50  tff(c_1247, plain, (![A_173, C_174]: (r1_tarski(k1_tarski(A_173), C_174) | ~r2_hidden(A_173, C_174) | ~r2_hidden(A_173, C_174))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1036])).
% 3.14/1.50  tff(c_40, plain, (![A_22, B_23]: (k2_xboole_0(A_22, B_23)=B_23 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.50  tff(c_1267, plain, (![A_175, C_176]: (k2_xboole_0(k1_tarski(A_175), C_176)=C_176 | ~r2_hidden(A_175, C_176))), inference(resolution, [status(thm)], [c_1247, c_40])).
% 3.14/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.50  tff(c_1350, plain, (![C_178, A_179]: (k2_xboole_0(C_178, k1_tarski(A_179))=C_178 | ~r2_hidden(A_179, C_178))), inference(superposition, [status(thm), theory('equality')], [c_1267, c_2])).
% 3.14/1.50  tff(c_42, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.50  tff(c_72, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.50  tff(c_76, plain, (k2_xboole_0(k1_tarski('#skF_4'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_72])).
% 3.14/1.50  tff(c_77, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42, c_76])).
% 3.14/1.50  tff(c_1374, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1350, c_77])).
% 3.14/1.50  tff(c_1405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1374])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 301
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 2
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 44
% 3.14/1.50  #Demod        : 99
% 3.14/1.50  #Tautology    : 169
% 3.14/1.50  #SimpNegUnit  : 4
% 3.14/1.50  #BackRed      : 0
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.50  Preprocessing        : 0.34
% 3.14/1.50  Parsing              : 0.17
% 3.14/1.50  CNF conversion       : 0.03
% 3.14/1.50  Main loop            : 0.41
% 3.14/1.50  Inferencing          : 0.15
% 3.14/1.50  Reduction            : 0.14
% 3.14/1.50  Demodulation         : 0.11
% 3.14/1.50  BG Simplification    : 0.02
% 3.14/1.50  Subsumption          : 0.08
% 3.14/1.50  Abstraction          : 0.02
% 3.14/1.50  MUC search           : 0.00
% 3.14/1.50  Cooper               : 0.00
% 3.14/1.50  Total                : 0.78
% 3.14/1.50  Index Insertion      : 0.00
% 3.14/1.50  Index Deletion       : 0.00
% 3.14/1.50  Index Matching       : 0.00
% 3.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
