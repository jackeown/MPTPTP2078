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
% DateTime   : Thu Dec  3 09:51:17 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_45,axiom,(
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

tff(c_24,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(k2_tarski(A_36,B_37),C_38)
      | ~ r2_hidden(B_37,C_38)
      | ~ r2_hidden(A_36,C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_112,plain,(
    ! [A_39,B_40,C_41] :
      ( k2_xboole_0(k2_tarski(A_39,B_40),C_41) = C_41
      | ~ r2_hidden(B_40,C_41)
      | ~ r2_hidden(A_39,C_41) ) ),
    inference(resolution,[status(thm)],[c_99,c_25])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [C_42,A_43,B_44] :
      ( k2_xboole_0(C_42,k2_tarski(A_43,B_44)) = C_42
      | ~ r2_hidden(B_44,C_42)
      | ~ r2_hidden(A_43,C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_153,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_26])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.24  
% 1.90/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.24  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.90/1.24  
% 1.90/1.24  %Foreground sorts:
% 1.90/1.24  
% 1.90/1.24  
% 1.90/1.24  %Background operators:
% 1.90/1.24  
% 1.90/1.24  
% 1.90/1.24  %Foreground operators:
% 1.90/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.24  
% 1.95/1.25  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 1.95/1.25  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.95/1.25  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.95/1.25  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.95/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.95/1.25  tff(c_24, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.25  tff(c_22, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.25  tff(c_99, plain, (![A_36, B_37, C_38]: (r1_tarski(k2_tarski(A_36, B_37), C_38) | ~r2_hidden(B_37, C_38) | ~r2_hidden(A_36, C_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.25  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.25  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.25  tff(c_25, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.95/1.25  tff(c_112, plain, (![A_39, B_40, C_41]: (k2_xboole_0(k2_tarski(A_39, B_40), C_41)=C_41 | ~r2_hidden(B_40, C_41) | ~r2_hidden(A_39, C_41))), inference(resolution, [status(thm)], [c_99, c_25])).
% 1.95/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.25  tff(c_143, plain, (![C_42, A_43, B_44]: (k2_xboole_0(C_42, k2_tarski(A_43, B_44))=C_42 | ~r2_hidden(B_44, C_42) | ~r2_hidden(A_43, C_42))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2])).
% 1.95/1.25  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.25  tff(c_26, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 1.95/1.25  tff(c_153, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_26])).
% 1.95/1.25  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_153])).
% 1.95/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  Inference rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Ref     : 0
% 1.95/1.25  #Sup     : 36
% 1.95/1.25  #Fact    : 0
% 1.95/1.25  #Define  : 0
% 1.95/1.25  #Split   : 0
% 1.95/1.25  #Chain   : 0
% 1.95/1.25  #Close   : 0
% 1.95/1.25  
% 1.95/1.25  Ordering : KBO
% 1.95/1.25  
% 1.95/1.25  Simplification rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Subsume      : 0
% 1.95/1.25  #Demod        : 4
% 1.95/1.25  #Tautology    : 21
% 1.95/1.25  #SimpNegUnit  : 0
% 1.95/1.25  #BackRed      : 0
% 1.95/1.25  
% 1.95/1.25  #Partial instantiations: 0
% 1.95/1.25  #Strategies tried      : 1
% 1.95/1.25  
% 1.95/1.25  Timing (in seconds)
% 1.95/1.25  ----------------------
% 1.95/1.25  Preprocessing        : 0.31
% 1.95/1.25  Parsing              : 0.16
% 1.95/1.25  CNF conversion       : 0.02
% 1.95/1.25  Main loop            : 0.13
% 1.95/1.25  Inferencing          : 0.05
% 1.95/1.25  Reduction            : 0.04
% 1.95/1.25  Demodulation         : 0.03
% 1.95/1.25  BG Simplification    : 0.01
% 1.95/1.25  Subsumption          : 0.02
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.26  MUC search           : 0.00
% 1.95/1.26  Cooper               : 0.00
% 1.95/1.26  Total                : 0.46
% 1.95/1.26  Index Insertion      : 0.00
% 1.95/1.26  Index Deletion       : 0.00
% 1.95/1.26  Index Matching       : 0.00
% 1.95/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
