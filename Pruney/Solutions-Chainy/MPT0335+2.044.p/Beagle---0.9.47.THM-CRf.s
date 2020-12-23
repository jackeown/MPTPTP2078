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
% DateTime   : Thu Dec  3 09:54:59 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,B)
     => ( ( r2_hidden(C,B)
          & A != C )
        | k3_xboole_0(k2_tarski(A,C),B) = k1_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_18,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [C_16,B_15] :
      ( k3_xboole_0(k2_tarski(C_16,C_16),B_15) = k1_tarski(C_16)
      | ~ r2_hidden(C_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [C_24,B_25] :
      ( k3_xboole_0(k1_tarski(C_24),B_25) = k1_tarski(C_24)
      | ~ r2_hidden(C_24,B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_311,plain,(
    ! [B_35,C_36] :
      ( k3_xboole_0(B_35,k1_tarski(C_36)) = k1_tarski(C_36)
      | ~ r2_hidden(C_36,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_22,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_141,plain,(
    ! [A_29,B_30,C_31] : k3_xboole_0(k3_xboole_0(A_29,B_30),C_31) = k3_xboole_0(A_29,k3_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_190,plain,(
    ! [C_32] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_32)) = k3_xboole_0('#skF_1',C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_141])).

tff(c_210,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_190])).

tff(c_321,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_210])).

tff(c_371,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_321])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:08:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.32  
% 2.01/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.33  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.01/1.33  
% 2.01/1.33  %Foreground sorts:
% 2.01/1.33  
% 2.01/1.33  
% 2.01/1.33  %Background operators:
% 2.01/1.33  
% 2.01/1.33  
% 2.01/1.33  %Foreground operators:
% 2.01/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.33  
% 2.01/1.34  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 2.01/1.34  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.34  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, B) => ((r2_hidden(C, B) & ~(A = C)) | (k3_xboole_0(k2_tarski(A, C), B) = k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 2.01/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.01/1.34  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.01/1.34  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.01/1.34  tff(c_18, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.34  tff(c_20, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.34  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.34  tff(c_14, plain, (![C_16, B_15]: (k3_xboole_0(k2_tarski(C_16, C_16), B_15)=k1_tarski(C_16) | ~r2_hidden(C_16, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.34  tff(c_109, plain, (![C_24, B_25]: (k3_xboole_0(k1_tarski(C_24), B_25)=k1_tarski(C_24) | ~r2_hidden(C_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.01/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.34  tff(c_311, plain, (![B_35, C_36]: (k3_xboole_0(B_35, k1_tarski(C_36))=k1_tarski(C_36) | ~r2_hidden(C_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 2.01/1.34  tff(c_22, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.34  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.34  tff(c_100, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.34  tff(c_104, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_24, c_100])).
% 2.01/1.34  tff(c_141, plain, (![A_29, B_30, C_31]: (k3_xboole_0(k3_xboole_0(A_29, B_30), C_31)=k3_xboole_0(A_29, k3_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.34  tff(c_190, plain, (![C_32]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_32))=k3_xboole_0('#skF_1', C_32))), inference(superposition, [status(thm), theory('equality')], [c_104, c_141])).
% 2.01/1.34  tff(c_210, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_190])).
% 2.01/1.34  tff(c_321, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_311, c_210])).
% 2.01/1.34  tff(c_371, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_321])).
% 2.01/1.34  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_371])).
% 2.01/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.34  
% 2.01/1.34  Inference rules
% 2.01/1.34  ----------------------
% 2.01/1.34  #Ref     : 0
% 2.01/1.34  #Sup     : 91
% 2.01/1.34  #Fact    : 0
% 2.01/1.34  #Define  : 0
% 2.01/1.34  #Split   : 0
% 2.01/1.34  #Chain   : 0
% 2.01/1.34  #Close   : 0
% 2.01/1.34  
% 2.01/1.34  Ordering : KBO
% 2.01/1.34  
% 2.01/1.34  Simplification rules
% 2.01/1.34  ----------------------
% 2.01/1.34  #Subsume      : 1
% 2.01/1.34  #Demod        : 30
% 2.01/1.34  #Tautology    : 48
% 2.01/1.34  #SimpNegUnit  : 1
% 2.01/1.34  #BackRed      : 0
% 2.01/1.34  
% 2.01/1.34  #Partial instantiations: 0
% 2.01/1.34  #Strategies tried      : 1
% 2.01/1.34  
% 2.01/1.34  Timing (in seconds)
% 2.01/1.34  ----------------------
% 2.25/1.34  Preprocessing        : 0.28
% 2.25/1.34  Parsing              : 0.15
% 2.25/1.34  CNF conversion       : 0.02
% 2.25/1.34  Main loop            : 0.27
% 2.25/1.34  Inferencing          : 0.10
% 2.25/1.34  Reduction            : 0.11
% 2.25/1.34  Demodulation         : 0.09
% 2.25/1.34  BG Simplification    : 0.01
% 2.25/1.34  Subsumption          : 0.04
% 2.25/1.34  Abstraction          : 0.01
% 2.25/1.34  MUC search           : 0.00
% 2.25/1.34  Cooper               : 0.00
% 2.25/1.34  Total                : 0.58
% 2.25/1.34  Index Insertion      : 0.00
% 2.25/1.34  Index Deletion       : 0.00
% 2.25/1.34  Index Matching       : 0.00
% 2.25/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
