%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  49 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
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

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_26,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [B_30,A_31] : k3_tarski(k2_tarski(B_30,A_31)) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_18,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_18])).

tff(c_28,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_159,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_220,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_217])).

tff(c_160,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_18])).

tff(c_175,plain,(
    ! [A_33,B_32] : r1_tarski(A_33,k2_xboole_0(B_32,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_10])).

tff(c_242,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_175])).

tff(c_14,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,(
    ! [B_40,C_41,A_42] :
      ( r2_hidden(B_40,C_41)
      | ~ r1_tarski(k2_tarski(A_42,B_40),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_369,plain,(
    ! [A_53,C_54] :
      ( r2_hidden(A_53,C_54)
      | ~ r1_tarski(k1_tarski(A_53),C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_264])).

tff(c_372,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_242,c_369])).

tff(c_396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:52:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.11/1.23  
% 2.11/1.23  %Foreground sorts:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Background operators:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Foreground operators:
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.23  
% 2.11/1.24  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.11/1.24  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.11/1.24  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.24  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.11/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.24  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.24  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.11/1.24  tff(c_26, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.24  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.24  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.24  tff(c_74, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.24  tff(c_133, plain, (![B_30, A_31]: (k3_tarski(k2_tarski(B_30, A_31))=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_12, c_74])).
% 2.11/1.24  tff(c_18, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.24  tff(c_139, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(superposition, [status(thm), theory('equality')], [c_133, c_18])).
% 2.11/1.24  tff(c_28, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.24  tff(c_159, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_28])).
% 2.11/1.24  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.24  tff(c_217, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_159, c_2])).
% 2.11/1.24  tff(c_220, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_217])).
% 2.11/1.24  tff(c_160, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_133, c_18])).
% 2.11/1.24  tff(c_175, plain, (![A_33, B_32]: (r1_tarski(A_33, k2_xboole_0(B_32, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_10])).
% 2.11/1.24  tff(c_242, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_220, c_175])).
% 2.11/1.24  tff(c_14, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.24  tff(c_264, plain, (![B_40, C_41, A_42]: (r2_hidden(B_40, C_41) | ~r1_tarski(k2_tarski(A_42, B_40), C_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.24  tff(c_369, plain, (![A_53, C_54]: (r2_hidden(A_53, C_54) | ~r1_tarski(k1_tarski(A_53), C_54))), inference(superposition, [status(thm), theory('equality')], [c_14, c_264])).
% 2.11/1.24  tff(c_372, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_242, c_369])).
% 2.11/1.24  tff(c_396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_372])).
% 2.11/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  Inference rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Ref     : 0
% 2.11/1.24  #Sup     : 88
% 2.11/1.24  #Fact    : 0
% 2.11/1.24  #Define  : 0
% 2.11/1.24  #Split   : 1
% 2.11/1.24  #Chain   : 0
% 2.11/1.24  #Close   : 0
% 2.11/1.24  
% 2.11/1.24  Ordering : KBO
% 2.11/1.24  
% 2.11/1.24  Simplification rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Subsume      : 4
% 2.11/1.24  #Demod        : 25
% 2.11/1.24  #Tautology    : 49
% 2.11/1.24  #SimpNegUnit  : 1
% 2.11/1.24  #BackRed      : 2
% 2.11/1.24  
% 2.11/1.24  #Partial instantiations: 0
% 2.11/1.24  #Strategies tried      : 1
% 2.11/1.24  
% 2.11/1.24  Timing (in seconds)
% 2.11/1.24  ----------------------
% 2.11/1.25  Preprocessing        : 0.29
% 2.11/1.25  Parsing              : 0.16
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.21
% 2.11/1.25  Inferencing          : 0.07
% 2.11/1.25  Reduction            : 0.07
% 2.11/1.25  Demodulation         : 0.06
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.04
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.53
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
