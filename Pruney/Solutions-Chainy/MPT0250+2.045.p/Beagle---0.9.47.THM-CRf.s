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

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  37 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_18,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_312,plain,(
    ! [A_42,B_43] : k2_xboole_0(A_42,k2_xboole_0(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_21,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_199,plain,(
    k2_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_21,c_181])).

tff(c_220,plain,(
    k2_xboole_0('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_199])).

tff(c_321,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_220])).

tff(c_32,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [A_18,B_17] : r1_tarski(A_18,k2_xboole_0(B_17,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_94,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | ~ r1_tarski(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_25,B_17] : r2_hidden(A_25,k2_xboole_0(B_17,k1_tarski(A_25))) ),
    inference(resolution,[status(thm)],[c_47,c_94])).

tff(c_398,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_107])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:25:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.15/1.31  
% 2.15/1.31  %Foreground sorts:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Background operators:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Foreground operators:
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.31  
% 2.15/1.32  tff(f_48, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.15/1.32  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.15/1.32  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.15/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.15/1.32  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.15/1.32  tff(c_18, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.32  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.32  tff(c_181, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.32  tff(c_312, plain, (![A_42, B_43]: (k2_xboole_0(A_42, k2_xboole_0(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_181])).
% 2.15/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.32  tff(c_20, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.32  tff(c_21, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.15/1.32  tff(c_199, plain, (k2_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_21, c_181])).
% 2.15/1.32  tff(c_220, plain, (k2_xboole_0('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_199])).
% 2.15/1.32  tff(c_321, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_312, c_220])).
% 2.15/1.32  tff(c_32, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.32  tff(c_47, plain, (![A_18, B_17]: (r1_tarski(A_18, k2_xboole_0(B_17, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 2.15/1.32  tff(c_94, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | ~r1_tarski(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.32  tff(c_107, plain, (![A_25, B_17]: (r2_hidden(A_25, k2_xboole_0(B_17, k1_tarski(A_25))))), inference(resolution, [status(thm)], [c_47, c_94])).
% 2.15/1.32  tff(c_398, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_321, c_107])).
% 2.15/1.32  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_398])).
% 2.15/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  Inference rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Ref     : 0
% 2.15/1.32  #Sup     : 97
% 2.15/1.32  #Fact    : 0
% 2.15/1.32  #Define  : 0
% 2.15/1.32  #Split   : 0
% 2.15/1.32  #Chain   : 0
% 2.15/1.32  #Close   : 0
% 2.15/1.32  
% 2.15/1.32  Ordering : KBO
% 2.15/1.32  
% 2.15/1.32  Simplification rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Subsume      : 3
% 2.15/1.32  #Demod        : 42
% 2.15/1.32  #Tautology    : 62
% 2.15/1.32  #SimpNegUnit  : 1
% 2.15/1.32  #BackRed      : 3
% 2.15/1.32  
% 2.15/1.32  #Partial instantiations: 0
% 2.15/1.32  #Strategies tried      : 1
% 2.15/1.32  
% 2.15/1.32  Timing (in seconds)
% 2.15/1.32  ----------------------
% 2.15/1.33  Preprocessing        : 0.30
% 2.15/1.33  Parsing              : 0.16
% 2.15/1.33  CNF conversion       : 0.02
% 2.15/1.33  Main loop            : 0.21
% 2.15/1.33  Inferencing          : 0.08
% 2.15/1.33  Reduction            : 0.08
% 2.15/1.33  Demodulation         : 0.06
% 2.15/1.33  BG Simplification    : 0.01
% 2.15/1.33  Subsumption          : 0.03
% 2.15/1.33  Abstraction          : 0.01
% 2.15/1.33  MUC search           : 0.00
% 2.15/1.33  Cooper               : 0.00
% 2.15/1.33  Total                : 0.53
% 2.15/1.33  Index Insertion      : 0.00
% 2.15/1.33  Index Deletion       : 0.00
% 2.15/1.33  Index Matching       : 0.00
% 2.15/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
