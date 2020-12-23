%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:18 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_71,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),B_16)
      | r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),B_10) = k1_xboole_0
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_108,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),k1_xboole_0) = k3_xboole_0(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_108])).

tff(c_181,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(k1_tarski(A_26),B_27) = k1_tarski(A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_294,plain,(
    ! [A_30,A_31] :
      ( k3_xboole_0(A_30,k1_tarski(A_31)) = k1_tarski(A_31)
      | ~ r2_hidden(A_31,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_181])).

tff(c_16,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_19,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_314,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_19])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.27  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.91/1.27  
% 1.91/1.27  %Foreground sorts:
% 1.91/1.27  
% 1.91/1.27  
% 1.91/1.27  %Background operators:
% 1.91/1.27  
% 1.91/1.27  
% 1.91/1.27  %Foreground operators:
% 1.91/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.27  
% 1.91/1.28  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.91/1.28  tff(f_47, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.91/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.91/1.28  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.91/1.28  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.91/1.28  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/1.28  tff(c_71, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), B_16) | r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.28  tff(c_18, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.28  tff(c_75, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_71, c_18])).
% 1.91/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.28  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.28  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.28  tff(c_108, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.28  tff(c_131, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), k1_xboole_0)=k3_xboole_0(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_108])).
% 1.91/1.28  tff(c_181, plain, (![A_26, B_27]: (k3_xboole_0(k1_tarski(A_26), B_27)=k1_tarski(A_26) | ~r2_hidden(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_131])).
% 1.91/1.28  tff(c_294, plain, (![A_30, A_31]: (k3_xboole_0(A_30, k1_tarski(A_31))=k1_tarski(A_31) | ~r2_hidden(A_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_181])).
% 1.91/1.28  tff(c_16, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.28  tff(c_19, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.91/1.28  tff(c_314, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_294, c_19])).
% 1.91/1.28  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_314])).
% 1.91/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.28  
% 1.91/1.28  Inference rules
% 1.91/1.28  ----------------------
% 1.91/1.28  #Ref     : 0
% 1.91/1.28  #Sup     : 76
% 1.91/1.28  #Fact    : 0
% 1.91/1.28  #Define  : 0
% 1.91/1.28  #Split   : 0
% 1.91/1.28  #Chain   : 0
% 1.91/1.28  #Close   : 0
% 1.91/1.28  
% 1.91/1.28  Ordering : KBO
% 1.91/1.28  
% 1.91/1.28  Simplification rules
% 1.91/1.28  ----------------------
% 1.91/1.28  #Subsume      : 7
% 1.91/1.28  #Demod        : 25
% 1.91/1.28  #Tautology    : 33
% 1.91/1.28  #SimpNegUnit  : 0
% 1.91/1.28  #BackRed      : 0
% 1.91/1.28  
% 1.91/1.28  #Partial instantiations: 0
% 1.91/1.28  #Strategies tried      : 1
% 1.91/1.28  
% 1.91/1.28  Timing (in seconds)
% 1.91/1.28  ----------------------
% 1.91/1.28  Preprocessing        : 0.29
% 1.91/1.28  Parsing              : 0.16
% 1.91/1.28  CNF conversion       : 0.02
% 1.91/1.28  Main loop            : 0.18
% 1.91/1.28  Inferencing          : 0.07
% 1.91/1.28  Reduction            : 0.06
% 1.91/1.28  Demodulation         : 0.05
% 1.91/1.28  BG Simplification    : 0.01
% 1.91/1.28  Subsumption          : 0.03
% 1.91/1.28  Abstraction          : 0.01
% 1.91/1.28  MUC search           : 0.00
% 1.91/1.28  Cooper               : 0.00
% 1.91/1.28  Total                : 0.49
% 1.91/1.28  Index Insertion      : 0.00
% 1.91/1.28  Index Deletion       : 0.00
% 1.91/1.28  Index Matching       : 0.00
% 1.91/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
