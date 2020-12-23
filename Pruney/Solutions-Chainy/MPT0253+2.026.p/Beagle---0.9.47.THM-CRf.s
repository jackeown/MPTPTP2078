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
% DateTime   : Thu Dec  3 09:51:17 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(k2_tarski(A_30,B_31),C_32)
      | ~ r2_hidden(B_31,C_32)
      | ~ r2_hidden(A_30,C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_23,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_101,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_xboole_0(k2_tarski(A_33,B_34),C_35) = C_35
      | ~ r2_hidden(B_34,C_35)
      | ~ r2_hidden(A_33,C_35) ) ),
    inference(resolution,[status(thm)],[c_88,c_23])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [C_36,A_37,B_38] :
      ( k2_xboole_0(C_36,k2_tarski(A_37,B_38)) = C_36
      | ~ r2_hidden(B_38,C_36)
      | ~ r2_hidden(A_37,C_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_148,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  %$ r2_hidden > r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.64/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.14  
% 1.64/1.14  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 1.64/1.14  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.64/1.14  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.64/1.14  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.64/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.64/1.14  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.14  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.14  tff(c_88, plain, (![A_30, B_31, C_32]: (r1_tarski(k2_tarski(A_30, B_31), C_32) | ~r2_hidden(B_31, C_32) | ~r2_hidden(A_30, C_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.14  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.14  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.14  tff(c_23, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.64/1.14  tff(c_101, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k2_tarski(A_33, B_34), C_35)=C_35 | ~r2_hidden(B_34, C_35) | ~r2_hidden(A_33, C_35))), inference(resolution, [status(thm)], [c_88, c_23])).
% 1.64/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.14  tff(c_132, plain, (![C_36, A_37, B_38]: (k2_xboole_0(C_36, k2_tarski(A_37, B_38))=C_36 | ~r2_hidden(B_38, C_36) | ~r2_hidden(A_37, C_36))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2])).
% 1.64/1.14  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.14  tff(c_24, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 1.64/1.14  tff(c_148, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 1.64/1.14  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_148])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 34
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 0
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.15  
% 1.64/1.15  Ordering : KBO
% 1.64/1.15  
% 1.64/1.15  Simplification rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Subsume      : 2
% 1.64/1.15  #Demod        : 4
% 1.64/1.15  #Tautology    : 19
% 1.64/1.15  #SimpNegUnit  : 0
% 1.64/1.15  #BackRed      : 0
% 1.64/1.15  
% 1.64/1.15  #Partial instantiations: 0
% 1.64/1.15  #Strategies tried      : 1
% 1.64/1.15  
% 1.64/1.15  Timing (in seconds)
% 1.64/1.15  ----------------------
% 1.64/1.15  Preprocessing        : 0.27
% 1.64/1.15  Parsing              : 0.15
% 1.64/1.15  CNF conversion       : 0.02
% 1.64/1.15  Main loop            : 0.12
% 1.64/1.15  Inferencing          : 0.05
% 1.64/1.15  Reduction            : 0.04
% 1.64/1.15  Demodulation         : 0.03
% 1.64/1.15  BG Simplification    : 0.01
% 1.64/1.15  Subsumption          : 0.02
% 1.64/1.15  Abstraction          : 0.01
% 1.64/1.15  MUC search           : 0.00
% 1.64/1.15  Cooper               : 0.00
% 1.64/1.15  Total                : 0.42
% 1.64/1.15  Index Insertion      : 0.00
% 1.64/1.15  Index Deletion       : 0.00
% 1.64/1.15  Index Matching       : 0.00
% 1.64/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
