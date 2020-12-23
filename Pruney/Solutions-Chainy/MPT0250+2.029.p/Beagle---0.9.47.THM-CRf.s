%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  44 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_34,A_35] : k3_tarski(k2_tarski(B_34,A_35)) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_20,plain,(
    ! [A_12,B_13] : k3_tarski(k2_tarski(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_20])).

tff(c_24,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_24])).

tff(c_262,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_177,c_262])).

tff(c_277,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_264])).

tff(c_178,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_20])).

tff(c_117,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | ~ r1_tarski(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_126,plain,(
    ! [A_25,B_4] : r2_hidden(A_25,k2_xboole_0(k1_tarski(A_25),B_4)) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_194,plain,(
    ! [A_25,B_36] : r2_hidden(A_25,k2_xboole_0(B_36,k1_tarski(A_25))) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_126])).

tff(c_291,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_194])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.21  
% 2.00/1.22  tff(f_50, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.00/1.22  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.00/1.22  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.00/1.22  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.00/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.00/1.22  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.00/1.22  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.22  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.22  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.22  tff(c_79, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.22  tff(c_151, plain, (![B_34, A_35]: (k3_tarski(k2_tarski(B_34, A_35))=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_10, c_79])).
% 2.00/1.22  tff(c_20, plain, (![A_12, B_13]: (k3_tarski(k2_tarski(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.22  tff(c_157, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_151, c_20])).
% 2.00/1.22  tff(c_24, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.22  tff(c_177, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_24])).
% 2.00/1.22  tff(c_262, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.22  tff(c_264, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_177, c_262])).
% 2.00/1.22  tff(c_277, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_264])).
% 2.00/1.22  tff(c_178, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_151, c_20])).
% 2.00/1.22  tff(c_117, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | ~r1_tarski(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.22  tff(c_126, plain, (![A_25, B_4]: (r2_hidden(A_25, k2_xboole_0(k1_tarski(A_25), B_4)))), inference(resolution, [status(thm)], [c_8, c_117])).
% 2.00/1.22  tff(c_194, plain, (![A_25, B_36]: (r2_hidden(A_25, k2_xboole_0(B_36, k1_tarski(A_25))))), inference(superposition, [status(thm), theory('equality')], [c_178, c_126])).
% 2.00/1.22  tff(c_291, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_277, c_194])).
% 2.00/1.22  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_291])).
% 2.00/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.22  
% 2.00/1.22  Inference rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Ref     : 0
% 2.00/1.22  #Sup     : 65
% 2.00/1.22  #Fact    : 0
% 2.00/1.22  #Define  : 0
% 2.00/1.22  #Split   : 0
% 2.00/1.22  #Chain   : 0
% 2.00/1.22  #Close   : 0
% 2.00/1.22  
% 2.00/1.22  Ordering : KBO
% 2.00/1.22  
% 2.00/1.22  Simplification rules
% 2.00/1.22  ----------------------
% 2.00/1.22  #Subsume      : 2
% 2.00/1.22  #Demod        : 19
% 2.00/1.22  #Tautology    : 46
% 2.00/1.22  #SimpNegUnit  : 1
% 2.00/1.22  #BackRed      : 2
% 2.00/1.22  
% 2.00/1.22  #Partial instantiations: 0
% 2.00/1.22  #Strategies tried      : 1
% 2.00/1.22  
% 2.00/1.22  Timing (in seconds)
% 2.00/1.22  ----------------------
% 2.00/1.23  Preprocessing        : 0.29
% 2.00/1.23  Parsing              : 0.15
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.18
% 2.00/1.23  Inferencing          : 0.07
% 2.00/1.23  Reduction            : 0.06
% 2.00/1.23  Demodulation         : 0.05
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.03
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.49
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
