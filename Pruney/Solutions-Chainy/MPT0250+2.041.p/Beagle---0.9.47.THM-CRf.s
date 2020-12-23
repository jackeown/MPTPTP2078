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
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  44 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_352,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_358,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_39,c_352])).

tff(c_367,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_358])).

tff(c_108,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_129,plain,(
    ! [A_40,B_39] : r1_tarski(A_40,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_24])).

tff(c_385,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_129])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_422,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_385,c_12])).

tff(c_26,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_397,plain,(
    ! [A_53,C_54,B_55] :
      ( r2_hidden(A_53,C_54)
      | ~ r1_tarski(k2_tarski(A_53,B_55),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_481,plain,(
    ! [A_59,B_60,B_61] : r2_hidden(A_59,k2_xboole_0(k2_tarski(A_59,B_60),B_61)) ),
    inference(resolution,[status(thm)],[c_24,c_397])).

tff(c_503,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_xboole_0(k1_tarski(A_62),B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_481])).

tff(c_506,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_503])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_506])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.05/1.27  
% 2.05/1.27  %Foreground sorts:
% 2.05/1.27  
% 2.05/1.27  
% 2.05/1.27  %Background operators:
% 2.05/1.27  
% 2.05/1.27  
% 2.05/1.27  %Foreground operators:
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.05/1.27  
% 2.05/1.28  tff(f_68, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.05/1.28  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.05/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.05/1.28  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.05/1.28  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.05/1.28  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.28  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.05/1.28  tff(c_34, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.05/1.28  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.28  tff(c_36, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.05/1.28  tff(c_39, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.05/1.28  tff(c_352, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.28  tff(c_358, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_39, c_352])).
% 2.05/1.28  tff(c_367, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_358])).
% 2.05/1.28  tff(c_108, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.28  tff(c_129, plain, (![A_40, B_39]: (r1_tarski(A_40, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_24])).
% 2.05/1.28  tff(c_385, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_367, c_129])).
% 2.05/1.28  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.28  tff(c_422, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_385, c_12])).
% 2.05/1.28  tff(c_26, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.28  tff(c_397, plain, (![A_53, C_54, B_55]: (r2_hidden(A_53, C_54) | ~r1_tarski(k2_tarski(A_53, B_55), C_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.05/1.28  tff(c_481, plain, (![A_59, B_60, B_61]: (r2_hidden(A_59, k2_xboole_0(k2_tarski(A_59, B_60), B_61)))), inference(resolution, [status(thm)], [c_24, c_397])).
% 2.05/1.28  tff(c_503, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_xboole_0(k1_tarski(A_62), B_63)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_481])).
% 2.05/1.28  tff(c_506, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_422, c_503])).
% 2.05/1.28  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_506])).
% 2.05/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.28  
% 2.05/1.28  Inference rules
% 2.05/1.28  ----------------------
% 2.05/1.28  #Ref     : 0
% 2.05/1.28  #Sup     : 121
% 2.05/1.28  #Fact    : 0
% 2.05/1.28  #Define  : 0
% 2.05/1.28  #Split   : 0
% 2.05/1.28  #Chain   : 0
% 2.05/1.28  #Close   : 0
% 2.05/1.28  
% 2.05/1.28  Ordering : KBO
% 2.05/1.28  
% 2.05/1.28  Simplification rules
% 2.05/1.28  ----------------------
% 2.05/1.28  #Subsume      : 0
% 2.05/1.28  #Demod        : 65
% 2.05/1.28  #Tautology    : 91
% 2.05/1.28  #SimpNegUnit  : 1
% 2.05/1.28  #BackRed      : 3
% 2.05/1.28  
% 2.05/1.28  #Partial instantiations: 0
% 2.05/1.28  #Strategies tried      : 1
% 2.05/1.28  
% 2.05/1.28  Timing (in seconds)
% 2.05/1.28  ----------------------
% 2.05/1.29  Preprocessing        : 0.28
% 2.05/1.29  Parsing              : 0.15
% 2.05/1.29  CNF conversion       : 0.02
% 2.05/1.29  Main loop            : 0.21
% 2.05/1.29  Inferencing          : 0.07
% 2.05/1.29  Reduction            : 0.08
% 2.05/1.29  Demodulation         : 0.06
% 2.05/1.29  BG Simplification    : 0.01
% 2.05/1.29  Subsumption          : 0.03
% 2.05/1.29  Abstraction          : 0.01
% 2.05/1.29  MUC search           : 0.00
% 2.05/1.29  Cooper               : 0.00
% 2.05/1.29  Total                : 0.52
% 2.05/1.29  Index Insertion      : 0.00
% 2.05/1.29  Index Deletion       : 0.00
% 2.05/1.29  Index Matching       : 0.00
% 2.05/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
