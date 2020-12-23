%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:19 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  42 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_118,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(k1_tarski(A_41),B_42) = k1_tarski(A_41)
      | r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_30])).

tff(c_140,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_93])).

tff(c_12,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(k2_tarski(A_50,B_51),C_52)
      | ~ r2_hidden(B_51,C_52)
      | ~ r2_hidden(A_50,C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_207,plain,(
    ! [A_53,C_54] :
      ( r1_tarski(k1_tarski(A_53),C_54)
      | ~ r2_hidden(A_53,C_54)
      | ~ r2_hidden(A_53,C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [A_55,C_56] :
      ( k3_xboole_0(k1_tarski(A_55),C_56) = k1_tarski(A_55)
      | ~ r2_hidden(A_55,C_56) ) ),
    inference(resolution,[status(thm)],[c_207,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_242,plain,(
    ! [C_57,A_58] :
      ( k3_xboole_0(C_57,k1_tarski(A_58)) = k1_tarski(A_58)
      | ~ r2_hidden(A_58,C_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_2])).

tff(c_28,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_31,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_255,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_31])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.92/1.19  
% 1.92/1.19  %Foreground sorts:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Background operators:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Foreground operators:
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.19  
% 1.99/1.20  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.99/1.20  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.99/1.20  tff(f_59, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.99/1.20  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.20  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.99/1.20  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.99/1.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.20  tff(c_118, plain, (![A_41, B_42]: (k4_xboole_0(k1_tarski(A_41), B_42)=k1_tarski(A_41) | r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.20  tff(c_85, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k4_xboole_0(A_29, B_30)!=A_29)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.20  tff(c_30, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.20  tff(c_93, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_85, c_30])).
% 1.99/1.20  tff(c_140, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_118, c_93])).
% 1.99/1.20  tff(c_12, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.20  tff(c_191, plain, (![A_50, B_51, C_52]: (r1_tarski(k2_tarski(A_50, B_51), C_52) | ~r2_hidden(B_51, C_52) | ~r2_hidden(A_50, C_52))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.20  tff(c_207, plain, (![A_53, C_54]: (r1_tarski(k1_tarski(A_53), C_54) | ~r2_hidden(A_53, C_54) | ~r2_hidden(A_53, C_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191])).
% 1.99/1.20  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.20  tff(c_216, plain, (![A_55, C_56]: (k3_xboole_0(k1_tarski(A_55), C_56)=k1_tarski(A_55) | ~r2_hidden(A_55, C_56))), inference(resolution, [status(thm)], [c_207, c_4])).
% 1.99/1.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.20  tff(c_242, plain, (![C_57, A_58]: (k3_xboole_0(C_57, k1_tarski(A_58))=k1_tarski(A_58) | ~r2_hidden(A_58, C_57))), inference(superposition, [status(thm), theory('equality')], [c_216, c_2])).
% 1.99/1.20  tff(c_28, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.20  tff(c_31, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 1.99/1.20  tff(c_255, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_242, c_31])).
% 1.99/1.20  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_255])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 61
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 0
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 1
% 1.99/1.20  #Demod        : 3
% 1.99/1.20  #Tautology    : 29
% 1.99/1.20  #SimpNegUnit  : 0
% 1.99/1.20  #BackRed      : 0
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.20  Preprocessing        : 0.28
% 1.99/1.20  Parsing              : 0.15
% 1.99/1.20  CNF conversion       : 0.02
% 1.99/1.20  Main loop            : 0.16
% 1.99/1.20  Inferencing          : 0.07
% 1.99/1.20  Reduction            : 0.05
% 1.99/1.20  Demodulation         : 0.04
% 1.99/1.20  BG Simplification    : 0.01
% 1.99/1.20  Subsumption          : 0.02
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.47
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
