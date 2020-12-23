%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:19 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_45,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),B_10)
      | r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_10])).

tff(c_50,plain,(
    ! [B_11,A_12] :
      ( k3_xboole_0(B_11,k1_tarski(A_12)) = k1_tarski(A_12)
      | ~ r2_hidden(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_11])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.14  
% 1.52/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.14  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.52/1.14  
% 1.52/1.14  %Foreground sorts:
% 1.52/1.14  
% 1.52/1.14  
% 1.52/1.14  %Background operators:
% 1.52/1.14  
% 1.52/1.14  
% 1.52/1.14  %Foreground operators:
% 1.52/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.52/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.52/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.52/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.52/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.52/1.14  
% 1.52/1.15  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 1.52/1.15  tff(f_41, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.52/1.15  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.52/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.52/1.15  tff(c_45, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), B_10) | r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.52/1.15  tff(c_10, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.52/1.15  tff(c_49, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_45, c_10])).
% 1.52/1.15  tff(c_50, plain, (![B_11, A_12]: (k3_xboole_0(B_11, k1_tarski(A_12))=k1_tarski(A_12) | ~r2_hidden(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.52/1.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.52/1.15  tff(c_8, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.52/1.15  tff(c_11, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 1.52/1.15  tff(c_62, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_11])).
% 1.52/1.15  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_62])).
% 1.52/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.52/1.15  
% 1.52/1.15  Inference rules
% 1.52/1.15  ----------------------
% 1.52/1.15  #Ref     : 0
% 1.52/1.15  #Sup     : 16
% 1.52/1.15  #Fact    : 0
% 1.52/1.15  #Define  : 0
% 1.52/1.15  #Split   : 0
% 1.52/1.15  #Chain   : 0
% 1.52/1.15  #Close   : 0
% 1.52/1.15  
% 1.52/1.15  Ordering : KBO
% 1.52/1.15  
% 1.52/1.15  Simplification rules
% 1.52/1.15  ----------------------
% 1.52/1.15  #Subsume      : 0
% 1.52/1.15  #Demod        : 2
% 1.52/1.15  #Tautology    : 9
% 1.52/1.15  #SimpNegUnit  : 0
% 1.52/1.15  #BackRed      : 0
% 1.52/1.15  
% 1.52/1.15  #Partial instantiations: 0
% 1.52/1.15  #Strategies tried      : 1
% 1.52/1.15  
% 1.52/1.15  Timing (in seconds)
% 1.52/1.15  ----------------------
% 1.52/1.15  Preprocessing        : 0.24
% 1.52/1.15  Parsing              : 0.13
% 1.52/1.15  CNF conversion       : 0.01
% 1.52/1.15  Main loop            : 0.08
% 1.52/1.15  Inferencing          : 0.04
% 1.52/1.16  Reduction            : 0.02
% 1.52/1.16  Demodulation         : 0.02
% 1.52/1.16  BG Simplification    : 0.01
% 1.52/1.16  Subsumption          : 0.01
% 1.52/1.16  Abstraction          : 0.00
% 1.52/1.16  MUC search           : 0.00
% 1.52/1.16  Cooper               : 0.00
% 1.52/1.16  Total                : 0.35
% 1.52/1.16  Index Insertion      : 0.00
% 1.52/1.16  Index Deletion       : 0.00
% 1.52/1.16  Index Matching       : 0.00
% 1.52/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
