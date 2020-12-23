%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:32 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   43 (  61 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  56 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_236,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k2_tarski(A_57,B_58),C_59)
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_258,plain,(
    ! [A_60,C_61] :
      ( r1_tarski(k1_tarski(A_60),C_61)
      | ~ r2_hidden(A_60,C_61)
      | ~ r2_hidden(A_60,C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_236])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_267,plain,(
    ! [A_62,C_63] :
      ( k2_xboole_0(k1_tarski(A_62),C_63) = C_63
      | ~ r2_hidden(A_62,C_63) ) ),
    inference(resolution,[status(thm)],[c_258,c_4])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(B_35,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_18,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [B_35,A_34] : k2_xboole_0(B_35,A_34) = k2_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_18])).

tff(c_354,plain,(
    ! [C_67,A_68] :
      ( k2_xboole_0(C_67,k1_tarski(A_68)) = C_67
      | ~ r2_hidden(A_68,C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_122])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_26])).

tff(c_177,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_178,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_177])).

tff(c_368,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_178])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:30:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.81  
% 2.46/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.81  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.46/1.81  
% 2.46/1.81  %Foreground sorts:
% 2.46/1.81  
% 2.46/1.81  
% 2.46/1.81  %Background operators:
% 2.46/1.81  
% 2.46/1.81  
% 2.46/1.81  %Foreground operators:
% 2.46/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.46/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.46/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.46/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.81  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.81  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.46/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.46/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.81  
% 2.53/1.83  tff(f_56, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.53/1.83  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.83  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.53/1.83  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.53/1.83  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.53/1.83  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.53/1.83  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.53/1.83  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.83  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.83  tff(c_236, plain, (![A_57, B_58, C_59]: (r1_tarski(k2_tarski(A_57, B_58), C_59) | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.83  tff(c_258, plain, (![A_60, C_61]: (r1_tarski(k1_tarski(A_60), C_61) | ~r2_hidden(A_60, C_61) | ~r2_hidden(A_60, C_61))), inference(superposition, [status(thm), theory('equality')], [c_10, c_236])).
% 2.53/1.83  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.83  tff(c_267, plain, (![A_62, C_63]: (k2_xboole_0(k1_tarski(A_62), C_63)=C_63 | ~r2_hidden(A_62, C_63))), inference(resolution, [status(thm)], [c_258, c_4])).
% 2.53/1.83  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.83  tff(c_80, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.83  tff(c_116, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_8, c_80])).
% 2.53/1.83  tff(c_18, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.83  tff(c_122, plain, (![B_35, A_34]: (k2_xboole_0(B_35, A_34)=k2_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_116, c_18])).
% 2.53/1.83  tff(c_354, plain, (![C_67, A_68]: (k2_xboole_0(C_67, k1_tarski(A_68))=C_67 | ~r2_hidden(A_68, C_67))), inference(superposition, [status(thm), theory('equality')], [c_267, c_122])).
% 2.53/1.83  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.53/1.83  tff(c_26, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.83  tff(c_175, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_26])).
% 2.53/1.83  tff(c_177, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_175])).
% 2.53/1.83  tff(c_178, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_177])).
% 2.53/1.83  tff(c_368, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_354, c_178])).
% 2.53/1.83  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_368])).
% 2.53/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.83  
% 2.53/1.83  Inference rules
% 2.53/1.83  ----------------------
% 2.53/1.83  #Ref     : 0
% 2.53/1.83  #Sup     : 94
% 2.53/1.83  #Fact    : 0
% 2.53/1.83  #Define  : 0
% 2.53/1.83  #Split   : 0
% 2.53/1.83  #Chain   : 0
% 2.53/1.83  #Close   : 0
% 2.53/1.83  
% 2.53/1.83  Ordering : KBO
% 2.53/1.83  
% 2.53/1.83  Simplification rules
% 2.53/1.83  ----------------------
% 2.53/1.83  #Subsume      : 12
% 2.53/1.83  #Demod        : 7
% 2.53/1.83  #Tautology    : 47
% 2.53/1.83  #SimpNegUnit  : 0
% 2.53/1.83  #BackRed      : 1
% 2.53/1.83  
% 2.53/1.83  #Partial instantiations: 0
% 2.53/1.83  #Strategies tried      : 1
% 2.53/1.83  
% 2.53/1.83  Timing (in seconds)
% 2.53/1.83  ----------------------
% 2.53/1.83  Preprocessing        : 0.53
% 2.53/1.83  Parsing              : 0.29
% 2.53/1.83  CNF conversion       : 0.03
% 2.57/1.84  Main loop            : 0.37
% 2.57/1.84  Inferencing          : 0.15
% 2.57/1.84  Reduction            : 0.12
% 2.57/1.84  Demodulation         : 0.10
% 2.57/1.84  BG Simplification    : 0.02
% 2.57/1.84  Subsumption          : 0.06
% 2.57/1.84  Abstraction          : 0.03
% 2.57/1.84  MUC search           : 0.00
% 2.57/1.84  Cooper               : 0.00
% 2.57/1.84  Total                : 0.94
% 2.57/1.84  Index Insertion      : 0.00
% 2.57/1.84  Index Deletion       : 0.00
% 2.57/1.84  Index Matching       : 0.00
% 2.57/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
