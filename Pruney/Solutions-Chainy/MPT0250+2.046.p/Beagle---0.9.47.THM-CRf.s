%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:38 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  34 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [A_29,B_28] : r1_tarski(A_29,k2_xboole_0(B_28,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_484,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,C_79)
      | ~ r1_tarski(B_80,C_79)
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_541,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,'#skF_2')
      | ~ r1_tarski(A_88,k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_29,c_484])).

tff(c_568,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_541])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_216,plain,(
    ! [B_40,C_41,A_42] :
      ( r2_hidden(B_40,C_41)
      | ~ r1_tarski(k2_tarski(A_42,B_40),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_235,plain,(
    ! [A_12,C_41] :
      ( r2_hidden(A_12,C_41)
      | ~ r1_tarski(k1_tarski(A_12),C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_579,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_568,c_235])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.32  
% 2.22/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.32  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.22/1.32  
% 2.22/1.32  %Foreground sorts:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Background operators:
% 2.22/1.32  
% 2.22/1.32  
% 2.22/1.32  %Foreground operators:
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.32  
% 2.52/1.33  tff(f_60, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.52/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.52/1.33  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.52/1.33  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.52/1.33  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.52/1.33  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.52/1.33  tff(c_26, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.33  tff(c_53, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.33  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.52/1.33  tff(c_68, plain, (![A_29, B_28]: (r1_tarski(A_29, k2_xboole_0(B_28, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_10])).
% 2.52/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.33  tff(c_28, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.52/1.33  tff(c_29, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 2.52/1.33  tff(c_484, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, C_79) | ~r1_tarski(B_80, C_79) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.33  tff(c_541, plain, (![A_88]: (r1_tarski(A_88, '#skF_2') | ~r1_tarski(A_88, k2_xboole_0('#skF_2', k1_tarski('#skF_1'))))), inference(resolution, [status(thm)], [c_29, c_484])).
% 2.52/1.33  tff(c_568, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_541])).
% 2.52/1.33  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.33  tff(c_216, plain, (![B_40, C_41, A_42]: (r2_hidden(B_40, C_41) | ~r1_tarski(k2_tarski(A_42, B_40), C_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.33  tff(c_235, plain, (![A_12, C_41]: (r2_hidden(A_12, C_41) | ~r1_tarski(k1_tarski(A_12), C_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_216])).
% 2.52/1.33  tff(c_579, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_568, c_235])).
% 2.52/1.33  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_579])).
% 2.52/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  Inference rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Ref     : 0
% 2.52/1.33  #Sup     : 122
% 2.52/1.33  #Fact    : 0
% 2.52/1.33  #Define  : 0
% 2.52/1.33  #Split   : 0
% 2.52/1.33  #Chain   : 0
% 2.52/1.33  #Close   : 0
% 2.52/1.33  
% 2.52/1.33  Ordering : KBO
% 2.52/1.33  
% 2.52/1.33  Simplification rules
% 2.52/1.33  ----------------------
% 2.52/1.33  #Subsume      : 5
% 2.52/1.33  #Demod        : 52
% 2.52/1.33  #Tautology    : 79
% 2.52/1.33  #SimpNegUnit  : 1
% 2.52/1.33  #BackRed      : 0
% 2.52/1.33  
% 2.52/1.33  #Partial instantiations: 0
% 2.52/1.33  #Strategies tried      : 1
% 2.52/1.33  
% 2.52/1.33  Timing (in seconds)
% 2.52/1.33  ----------------------
% 2.52/1.34  Preprocessing        : 0.30
% 2.52/1.34  Parsing              : 0.16
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.28
% 2.52/1.34  Inferencing          : 0.11
% 2.52/1.34  Reduction            : 0.10
% 2.52/1.34  Demodulation         : 0.08
% 2.52/1.34  BG Simplification    : 0.01
% 2.52/1.34  Subsumption          : 0.05
% 2.52/1.34  Abstraction          : 0.02
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.61
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
