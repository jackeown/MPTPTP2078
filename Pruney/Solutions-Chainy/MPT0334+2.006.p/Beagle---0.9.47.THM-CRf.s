%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:52 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,k1_tarski(B_24)) = A_23
      | r2_hidden(B_24,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_184,plain,(
    ! [C_56,B_57,A_58] :
      ( k4_xboole_0(k2_xboole_0(C_56,B_57),A_58) = k2_xboole_0(k4_xboole_0(C_56,A_58),B_57)
      | ~ r1_xboole_0(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_39,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_197,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_39])).

tff(c_217,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_223,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) != k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_217])).

tff(c_227,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_223])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_230,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_227,c_14])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.01/1.26  
% 2.01/1.26  %Foreground sorts:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Background operators:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Foreground operators:
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.01/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.26  
% 2.01/1.27  tff(f_63, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 2.01/1.27  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.01/1.27  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.01/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.01/1.27  tff(f_37, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 2.01/1.27  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.01/1.27  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.27  tff(c_34, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k1_tarski(B_24))=A_23 | r2_hidden(B_24, A_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.27  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.27  tff(c_184, plain, (![C_56, B_57, A_58]: (k4_xboole_0(k2_xboole_0(C_56, B_57), A_58)=k2_xboole_0(k4_xboole_0(C_56, A_58), B_57) | ~r1_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.27  tff(c_36, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.27  tff(c_39, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.01/1.27  tff(c_197, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4'))) | ~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_39])).
% 2.01/1.27  tff(c_217, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_197])).
% 2.01/1.27  tff(c_223, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))!=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_8, c_217])).
% 2.01/1.27  tff(c_227, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_223])).
% 2.01/1.27  tff(c_14, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.27  tff(c_230, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_227, c_14])).
% 2.01/1.27  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_230])).
% 2.01/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  Inference rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Ref     : 0
% 2.01/1.27  #Sup     : 44
% 2.01/1.27  #Fact    : 0
% 2.01/1.27  #Define  : 0
% 2.01/1.27  #Split   : 1
% 2.01/1.27  #Chain   : 0
% 2.01/1.27  #Close   : 0
% 2.01/1.27  
% 2.01/1.27  Ordering : KBO
% 2.01/1.27  
% 2.01/1.27  Simplification rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Subsume      : 0
% 2.01/1.27  #Demod        : 2
% 2.01/1.27  #Tautology    : 27
% 2.01/1.27  #SimpNegUnit  : 1
% 2.01/1.27  #BackRed      : 0
% 2.01/1.27  
% 2.01/1.27  #Partial instantiations: 0
% 2.01/1.27  #Strategies tried      : 1
% 2.01/1.27  
% 2.01/1.27  Timing (in seconds)
% 2.01/1.27  ----------------------
% 2.01/1.27  Preprocessing        : 0.32
% 2.01/1.27  Parsing              : 0.17
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.27  Main loop            : 0.17
% 2.01/1.27  Inferencing          : 0.06
% 2.01/1.27  Reduction            : 0.06
% 2.01/1.27  Demodulation         : 0.04
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.03
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.27  Total                : 0.51
% 2.01/1.27  Index Insertion      : 0.00
% 2.01/1.27  Index Deletion       : 0.00
% 2.01/1.27  Index Matching       : 0.00
% 2.01/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
