%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:18 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   30 (  35 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_60,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_16])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_24,C_25,B_26] :
      ( k3_xboole_0(k2_tarski(A_24,C_25),B_26) = k2_tarski(A_24,C_25)
      | ~ r2_hidden(C_25,B_26)
      | ~ r2_hidden(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [B_27,A_28,C_29] :
      ( k3_xboole_0(B_27,k2_tarski(A_28,C_29)) = k2_tarski(A_28,C_29)
      | ~ r2_hidden(C_29,B_27)
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2])).

tff(c_141,plain,(
    ! [B_27,A_3] :
      ( k3_xboole_0(B_27,k1_tarski(A_3)) = k2_tarski(A_3,A_3)
      | ~ r2_hidden(A_3,B_27)
      | ~ r2_hidden(A_3,B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_176,plain,(
    ! [B_32,A_33] :
      ( k3_xboole_0(B_32,k1_tarski(A_33)) = k1_tarski(A_33)
      | ~ r2_hidden(A_33,B_32)
      | ~ r2_hidden(A_33,B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_141])).

tff(c_14,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_17,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_196,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_17])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  
% 1.71/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.15  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.71/1.15  
% 1.71/1.15  %Foreground sorts:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Background operators:
% 1.71/1.15  
% 1.71/1.15  
% 1.71/1.15  %Foreground operators:
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.15  
% 1.71/1.16  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.71/1.16  tff(f_49, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.71/1.16  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.71/1.16  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 1.71/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.71/1.16  tff(c_60, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.71/1.16  tff(c_16, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.16  tff(c_64, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_16])).
% 1.71/1.16  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.16  tff(c_83, plain, (![A_24, C_25, B_26]: (k3_xboole_0(k2_tarski(A_24, C_25), B_26)=k2_tarski(A_24, C_25) | ~r2_hidden(C_25, B_26) | ~r2_hidden(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.16  tff(c_110, plain, (![B_27, A_28, C_29]: (k3_xboole_0(B_27, k2_tarski(A_28, C_29))=k2_tarski(A_28, C_29) | ~r2_hidden(C_29, B_27) | ~r2_hidden(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_83, c_2])).
% 1.71/1.16  tff(c_141, plain, (![B_27, A_3]: (k3_xboole_0(B_27, k1_tarski(A_3))=k2_tarski(A_3, A_3) | ~r2_hidden(A_3, B_27) | ~r2_hidden(A_3, B_27))), inference(superposition, [status(thm), theory('equality')], [c_4, c_110])).
% 1.71/1.16  tff(c_176, plain, (![B_32, A_33]: (k3_xboole_0(B_32, k1_tarski(A_33))=k1_tarski(A_33) | ~r2_hidden(A_33, B_32) | ~r2_hidden(A_33, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_141])).
% 1.71/1.16  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.71/1.16  tff(c_17, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.71/1.16  tff(c_196, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_17])).
% 1.71/1.16  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_196])).
% 1.71/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  Inference rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Ref     : 0
% 1.71/1.16  #Sup     : 50
% 1.71/1.16  #Fact    : 0
% 1.71/1.16  #Define  : 0
% 1.71/1.16  #Split   : 0
% 1.71/1.16  #Chain   : 0
% 1.71/1.16  #Close   : 0
% 1.71/1.16  
% 1.71/1.16  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 6
% 1.71/1.16  #Demod        : 4
% 1.71/1.16  #Tautology    : 21
% 1.71/1.16  #SimpNegUnit  : 0
% 1.71/1.16  #BackRed      : 0
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.16  Preprocessing        : 0.27
% 1.71/1.16  Parsing              : 0.15
% 1.71/1.16  CNF conversion       : 0.02
% 1.71/1.16  Main loop            : 0.14
% 1.71/1.16  Inferencing          : 0.06
% 1.71/1.16  Reduction            : 0.04
% 1.71/1.16  Demodulation         : 0.03
% 1.71/1.16  BG Simplification    : 0.01
% 1.71/1.16  Subsumption          : 0.02
% 1.71/1.16  Abstraction          : 0.01
% 1.71/1.16  MUC search           : 0.00
% 1.71/1.16  Cooper               : 0.00
% 1.71/1.16  Total                : 0.43
% 1.71/1.16  Index Insertion      : 0.00
% 1.71/1.16  Index Deletion       : 0.00
% 1.71/1.16  Index Matching       : 0.00
% 1.71/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
