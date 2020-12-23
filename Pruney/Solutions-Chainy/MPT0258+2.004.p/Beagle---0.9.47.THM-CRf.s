%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:07 EST 2020

% Result     : Theorem 5.16s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  55 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(k2_tarski(A_15,B_16),C_17)
      | ~ r2_hidden(B_16,C_17)
      | ~ r2_hidden(A_15,C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k3_xboole_0(B_52,C_53))
      | ~ r1_tarski(A_51,C_53)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [B_21,A_22] : k3_xboole_0(B_21,A_22) = k3_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [B_21,A_22] : r1_tarski(k3_xboole_0(B_21,A_22),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_10])).

tff(c_91,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [B_21,A_22] :
      ( k3_xboole_0(B_21,A_22) = A_22
      | ~ r1_tarski(A_22,k3_xboole_0(B_21,A_22)) ) ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_183,plain,(
    ! [B_52,C_53] :
      ( k3_xboole_0(B_52,C_53) = C_53
      | ~ r1_tarski(C_53,C_53)
      | ~ r1_tarski(C_53,B_52) ) ),
    inference(resolution,[status(thm)],[c_175,c_98])).

tff(c_272,plain,(
    ! [B_57,C_58] :
      ( k3_xboole_0(B_57,C_58) = C_58
      | ~ r1_tarski(C_58,B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_4542,plain,(
    ! [C_174,A_175,B_176] :
      ( k3_xboole_0(C_174,k2_tarski(A_175,B_176)) = k2_tarski(A_175,B_176)
      | ~ r2_hidden(B_176,C_174)
      | ~ r2_hidden(A_175,C_174) ) ),
    inference(resolution,[status(thm)],[c_18,c_272])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k2_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    k3_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_4708,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4542,c_30])).

tff(c_4795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_4708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.16/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/1.99  
% 5.16/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/1.99  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.16/1.99  
% 5.16/1.99  %Foreground sorts:
% 5.16/1.99  
% 5.16/1.99  
% 5.16/1.99  %Background operators:
% 5.16/1.99  
% 5.16/1.99  
% 5.16/1.99  %Foreground operators:
% 5.16/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.16/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.16/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.16/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.16/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.16/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.16/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.16/1.99  
% 5.16/2.00  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 5.16/2.00  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.16/2.00  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.16/2.00  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.16/2.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.16/2.00  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.16/2.00  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.16/2.00  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.16/2.00  tff(c_18, plain, (![A_15, B_16, C_17]: (r1_tarski(k2_tarski(A_15, B_16), C_17) | ~r2_hidden(B_16, C_17) | ~r2_hidden(A_15, C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.16/2.00  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.16/2.00  tff(c_175, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k3_xboole_0(B_52, C_53)) | ~r1_tarski(A_51, C_53) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.16/2.00  tff(c_33, plain, (![B_21, A_22]: (k3_xboole_0(B_21, A_22)=k3_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.00  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.16/2.00  tff(c_48, plain, (![B_21, A_22]: (r1_tarski(k3_xboole_0(B_21, A_22), A_22))), inference(superposition, [status(thm), theory('equality')], [c_33, c_10])).
% 5.16/2.00  tff(c_91, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.16/2.00  tff(c_98, plain, (![B_21, A_22]: (k3_xboole_0(B_21, A_22)=A_22 | ~r1_tarski(A_22, k3_xboole_0(B_21, A_22)))), inference(resolution, [status(thm)], [c_48, c_91])).
% 5.16/2.00  tff(c_183, plain, (![B_52, C_53]: (k3_xboole_0(B_52, C_53)=C_53 | ~r1_tarski(C_53, C_53) | ~r1_tarski(C_53, B_52))), inference(resolution, [status(thm)], [c_175, c_98])).
% 5.16/2.00  tff(c_272, plain, (![B_57, C_58]: (k3_xboole_0(B_57, C_58)=C_58 | ~r1_tarski(C_58, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_183])).
% 5.16/2.00  tff(c_4542, plain, (![C_174, A_175, B_176]: (k3_xboole_0(C_174, k2_tarski(A_175, B_176))=k2_tarski(A_175, B_176) | ~r2_hidden(B_176, C_174) | ~r2_hidden(A_175, C_174))), inference(resolution, [status(thm)], [c_18, c_272])).
% 5.16/2.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.00  tff(c_24, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k2_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.16/2.00  tff(c_30, plain, (k3_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 5.16/2.00  tff(c_4708, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4542, c_30])).
% 5.16/2.00  tff(c_4795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_4708])).
% 5.16/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.00  
% 5.16/2.00  Inference rules
% 5.16/2.00  ----------------------
% 5.16/2.00  #Ref     : 0
% 5.16/2.00  #Sup     : 1150
% 5.16/2.00  #Fact    : 0
% 5.16/2.00  #Define  : 0
% 5.16/2.00  #Split   : 0
% 5.16/2.00  #Chain   : 0
% 5.16/2.00  #Close   : 0
% 5.16/2.00  
% 5.16/2.00  Ordering : KBO
% 5.16/2.00  
% 5.16/2.00  Simplification rules
% 5.16/2.00  ----------------------
% 5.16/2.00  #Subsume      : 366
% 5.16/2.00  #Demod        : 1206
% 5.16/2.00  #Tautology    : 553
% 5.16/2.00  #SimpNegUnit  : 0
% 5.16/2.00  #BackRed      : 0
% 5.16/2.00  
% 5.16/2.00  #Partial instantiations: 0
% 5.16/2.00  #Strategies tried      : 1
% 5.16/2.00  
% 5.16/2.00  Timing (in seconds)
% 5.16/2.00  ----------------------
% 5.16/2.00  Preprocessing        : 0.29
% 5.16/2.00  Parsing              : 0.15
% 5.16/2.00  CNF conversion       : 0.02
% 5.16/2.00  Main loop            : 0.95
% 5.16/2.00  Inferencing          : 0.27
% 5.16/2.00  Reduction            : 0.43
% 5.16/2.00  Demodulation         : 0.37
% 5.16/2.00  BG Simplification    : 0.04
% 5.16/2.00  Subsumption          : 0.17
% 5.16/2.00  Abstraction          : 0.05
% 5.16/2.00  MUC search           : 0.00
% 5.16/2.00  Cooper               : 0.00
% 5.16/2.00  Total                : 1.26
% 5.16/2.00  Index Insertion      : 0.00
% 5.16/2.00  Index Deletion       : 0.00
% 5.16/2.00  Index Matching       : 0.00
% 5.16/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
