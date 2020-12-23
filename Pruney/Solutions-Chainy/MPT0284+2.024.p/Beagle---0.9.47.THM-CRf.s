%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:29 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),k5_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),k5_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(k2_xboole_0(A_34,C_35),B_36)
      | ~ r1_tarski(C_35,B_36)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_107,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_103,c_16])).

tff(c_108,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_111,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_116,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_120,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_116])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:59:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.20  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.82/1.20  
% 1.82/1.20  %Foreground sorts:
% 1.82/1.20  
% 1.82/1.20  
% 1.82/1.20  %Background operators:
% 1.82/1.20  
% 1.82/1.20  
% 1.82/1.20  %Foreground operators:
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.82/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.20  
% 1.82/1.21  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.82/1.21  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 1.82/1.21  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.82/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.82/1.21  tff(f_48, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 1.82/1.21  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.21  tff(c_68, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), k5_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.21  tff(c_71, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 1.82/1.21  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.21  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), k5_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.21  tff(c_103, plain, (![A_34, C_35, B_36]: (r1_tarski(k2_xboole_0(A_34, C_35), B_36) | ~r1_tarski(C_35, B_36) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.21  tff(c_16, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.21  tff(c_107, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_103, c_16])).
% 1.82/1.21  tff(c_108, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_107])).
% 1.82/1.21  tff(c_111, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_108])).
% 1.82/1.21  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 1.82/1.21  tff(c_116, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_107])).
% 1.82/1.21  tff(c_120, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_116])).
% 1.82/1.21  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_120])).
% 1.82/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  Inference rules
% 1.82/1.21  ----------------------
% 1.82/1.21  #Ref     : 0
% 1.82/1.21  #Sup     : 23
% 1.82/1.21  #Fact    : 0
% 1.82/1.21  #Define  : 0
% 1.82/1.21  #Split   : 1
% 1.82/1.21  #Chain   : 0
% 1.82/1.21  #Close   : 0
% 1.82/1.21  
% 1.82/1.21  Ordering : KBO
% 1.82/1.21  
% 1.82/1.21  Simplification rules
% 1.82/1.21  ----------------------
% 1.82/1.21  #Subsume      : 0
% 1.82/1.21  #Demod        : 5
% 1.82/1.21  #Tautology    : 17
% 1.82/1.21  #SimpNegUnit  : 0
% 1.82/1.21  #BackRed      : 0
% 1.82/1.21  
% 1.82/1.21  #Partial instantiations: 0
% 1.82/1.21  #Strategies tried      : 1
% 1.82/1.21  
% 1.82/1.21  Timing (in seconds)
% 1.82/1.21  ----------------------
% 1.82/1.21  Preprocessing        : 0.29
% 1.82/1.21  Parsing              : 0.15
% 1.82/1.21  CNF conversion       : 0.02
% 1.82/1.21  Main loop            : 0.12
% 1.82/1.21  Inferencing          : 0.05
% 1.82/1.21  Reduction            : 0.04
% 1.82/1.21  Demodulation         : 0.03
% 1.82/1.21  BG Simplification    : 0.01
% 1.82/1.21  Subsumption          : 0.01
% 1.82/1.21  Abstraction          : 0.01
% 1.82/1.21  MUC search           : 0.00
% 1.82/1.21  Cooper               : 0.00
% 1.82/1.21  Total                : 0.43
% 1.82/1.21  Index Insertion      : 0.00
% 1.82/1.21  Index Deletion       : 0.00
% 1.82/1.21  Index Matching       : 0.00
% 1.82/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
