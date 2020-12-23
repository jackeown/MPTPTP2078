%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:07 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  46 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_45,B_46,C_47] :
      ( r1_tarski(k2_tarski(A_45,B_46),C_47)
      | ~ r2_hidden(B_46,C_47)
      | ~ r2_hidden(A_45,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,k4_xboole_0(C_32,B_33))
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [A_40,C_41,B_42] :
      ( k4_xboole_0(A_40,k4_xboole_0(C_41,B_42)) = A_40
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [C_41,B_42] :
      ( k3_xboole_0(C_41,B_42) = C_41
      | ~ r1_tarski(C_41,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_4])).

tff(c_2207,plain,(
    ! [A_145,B_146,C_147] :
      ( k3_xboole_0(k2_tarski(A_145,B_146),C_147) = k2_tarski(A_145,B_146)
      | ~ r2_hidden(B_146,C_147)
      | ~ r2_hidden(A_145,C_147) ) ),
    inference(resolution,[status(thm)],[c_142,c_126])).

tff(c_2943,plain,(
    ! [B_181,A_182,B_183] :
      ( k3_xboole_0(B_181,k2_tarski(A_182,B_183)) = k2_tarski(A_182,B_183)
      | ~ r2_hidden(B_183,B_181)
      | ~ r2_hidden(A_182,B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2207])).

tff(c_22,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k2_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27,plain,(
    k3_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_3024,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_27])).

tff(c_3055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_3024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:50:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.87  
% 4.74/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 4.74/1.87  
% 4.74/1.87  %Foreground sorts:
% 4.74/1.87  
% 4.74/1.87  
% 4.74/1.87  %Background operators:
% 4.74/1.87  
% 4.74/1.87  
% 4.74/1.87  %Foreground operators:
% 4.74/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.74/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.74/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.74/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/1.87  
% 4.74/1.88  tff(f_54, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 4.74/1.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.74/1.88  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.74/1.88  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.74/1.88  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.74/1.88  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.74/1.88  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.74/1.88  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.74/1.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.74/1.88  tff(c_142, plain, (![A_45, B_46, C_47]: (r1_tarski(k2_tarski(A_45, B_46), C_47) | ~r2_hidden(B_46, C_47) | ~r2_hidden(A_45, C_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.74/1.88  tff(c_92, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, k4_xboole_0(C_32, B_33)) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.74/1.88  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.74/1.88  tff(c_110, plain, (![A_40, C_41, B_42]: (k4_xboole_0(A_40, k4_xboole_0(C_41, B_42))=A_40 | ~r1_tarski(A_40, B_42))), inference(resolution, [status(thm)], [c_92, c_6])).
% 4.74/1.88  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.74/1.88  tff(c_126, plain, (![C_41, B_42]: (k3_xboole_0(C_41, B_42)=C_41 | ~r1_tarski(C_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_110, c_4])).
% 4.74/1.88  tff(c_2207, plain, (![A_145, B_146, C_147]: (k3_xboole_0(k2_tarski(A_145, B_146), C_147)=k2_tarski(A_145, B_146) | ~r2_hidden(B_146, C_147) | ~r2_hidden(A_145, C_147))), inference(resolution, [status(thm)], [c_142, c_126])).
% 4.74/1.88  tff(c_2943, plain, (![B_181, A_182, B_183]: (k3_xboole_0(B_181, k2_tarski(A_182, B_183))=k2_tarski(A_182, B_183) | ~r2_hidden(B_183, B_181) | ~r2_hidden(A_182, B_181))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2207])).
% 4.74/1.88  tff(c_22, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k2_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.74/1.88  tff(c_27, plain, (k3_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 4.74/1.88  tff(c_3024, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2943, c_27])).
% 4.74/1.88  tff(c_3055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_3024])).
% 4.74/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.88  
% 4.74/1.88  Inference rules
% 4.74/1.88  ----------------------
% 4.74/1.88  #Ref     : 0
% 4.74/1.88  #Sup     : 909
% 4.74/1.88  #Fact    : 0
% 4.74/1.88  #Define  : 0
% 4.74/1.88  #Split   : 0
% 4.74/1.88  #Chain   : 0
% 4.74/1.88  #Close   : 0
% 4.74/1.88  
% 4.74/1.88  Ordering : KBO
% 4.74/1.88  
% 4.74/1.88  Simplification rules
% 4.74/1.88  ----------------------
% 4.74/1.88  #Subsume      : 123
% 4.74/1.88  #Demod        : 151
% 4.74/1.88  #Tautology    : 86
% 4.74/1.88  #SimpNegUnit  : 0
% 4.74/1.88  #BackRed      : 0
% 4.74/1.88  
% 4.74/1.88  #Partial instantiations: 0
% 4.74/1.88  #Strategies tried      : 1
% 4.74/1.88  
% 4.74/1.88  Timing (in seconds)
% 4.74/1.88  ----------------------
% 4.74/1.88  Preprocessing        : 0.28
% 4.74/1.88  Parsing              : 0.15
% 4.74/1.88  CNF conversion       : 0.02
% 4.74/1.88  Main loop            : 0.83
% 4.74/1.88  Inferencing          : 0.27
% 4.74/1.88  Reduction            : 0.29
% 4.74/1.88  Demodulation         : 0.24
% 4.74/1.88  BG Simplification    : 0.04
% 4.74/1.88  Subsumption          : 0.19
% 4.74/1.88  Abstraction          : 0.05
% 4.74/1.88  MUC search           : 0.00
% 4.74/1.88  Cooper               : 0.00
% 4.74/1.88  Total                : 1.14
% 4.74/1.88  Index Insertion      : 0.00
% 4.74/1.88  Index Deletion       : 0.00
% 4.74/1.88  Index Matching       : 0.00
% 4.74/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
