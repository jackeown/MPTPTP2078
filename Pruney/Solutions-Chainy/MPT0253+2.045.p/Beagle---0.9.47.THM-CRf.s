%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:19 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_30,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_205,plain,(
    ! [A_57,B_58,C_59] :
      ( r1_tarski(k2_tarski(A_57,B_58),C_59)
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_270,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_xboole_0(k2_tarski(A_63,B_64),C_65) = C_65
      | ~ r2_hidden(B_64,C_65)
      | ~ r2_hidden(A_63,C_65) ) ),
    inference(resolution,[status(thm)],[c_205,c_31])).

tff(c_26,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_280,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_26])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.17/1.34  
% 2.17/1.34  %Foreground sorts:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Background operators:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Foreground operators:
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.34  
% 2.17/1.35  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.17/1.35  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.17/1.35  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.17/1.35  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.17/1.35  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.35  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.35  tff(c_205, plain, (![A_57, B_58, C_59]: (r1_tarski(k2_tarski(A_57, B_58), C_59) | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.35  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.35  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.35  tff(c_31, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.17/1.35  tff(c_270, plain, (![A_63, B_64, C_65]: (k2_xboole_0(k2_tarski(A_63, B_64), C_65)=C_65 | ~r2_hidden(B_64, C_65) | ~r2_hidden(A_63, C_65))), inference(resolution, [status(thm)], [c_205, c_31])).
% 2.17/1.35  tff(c_26, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.35  tff(c_280, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_270, c_26])).
% 2.17/1.35  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_280])).
% 2.17/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  
% 2.17/1.35  Inference rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Ref     : 0
% 2.17/1.35  #Sup     : 63
% 2.17/1.35  #Fact    : 0
% 2.17/1.35  #Define  : 0
% 2.17/1.35  #Split   : 0
% 2.17/1.35  #Chain   : 0
% 2.17/1.35  #Close   : 0
% 2.17/1.35  
% 2.17/1.35  Ordering : KBO
% 2.17/1.35  
% 2.17/1.35  Simplification rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Subsume      : 0
% 2.17/1.35  #Demod        : 15
% 2.17/1.35  #Tautology    : 29
% 2.17/1.35  #SimpNegUnit  : 0
% 2.17/1.35  #BackRed      : 0
% 2.17/1.35  
% 2.17/1.35  #Partial instantiations: 0
% 2.17/1.35  #Strategies tried      : 1
% 2.17/1.35  
% 2.17/1.35  Timing (in seconds)
% 2.17/1.35  ----------------------
% 2.17/1.35  Preprocessing        : 0.32
% 2.17/1.35  Parsing              : 0.18
% 2.17/1.35  CNF conversion       : 0.02
% 2.17/1.35  Main loop            : 0.18
% 2.17/1.35  Inferencing          : 0.07
% 2.17/1.35  Reduction            : 0.06
% 2.17/1.35  Demodulation         : 0.05
% 2.17/1.35  BG Simplification    : 0.02
% 2.17/1.35  Subsumption          : 0.02
% 2.17/1.35  Abstraction          : 0.02
% 2.17/1.35  MUC search           : 0.00
% 2.17/1.35  Cooper               : 0.00
% 2.17/1.35  Total                : 0.52
% 2.17/1.35  Index Insertion      : 0.00
% 2.17/1.35  Index Deletion       : 0.00
% 2.17/1.35  Index Matching       : 0.00
% 2.17/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
