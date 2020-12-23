%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:07 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  56 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_30,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(k2_tarski(A_14,B_15),C_16)
      | ~ r2_hidden(B_15,C_16)
      | ~ r2_hidden(A_14,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski('#skF_1'(A_46,B_47,C_48),C_48)
      | k3_xboole_0(B_47,C_48) = A_46
      | ~ r1_tarski(A_46,C_48)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r1_tarski('#skF_1'(A_5,B_6,C_7),A_5)
      | k3_xboole_0(B_6,C_7) = A_5
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_137,plain,(
    ! [B_47,C_48] :
      ( k3_xboole_0(B_47,C_48) = C_48
      | ~ r1_tarski(C_48,C_48)
      | ~ r1_tarski(C_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_133,c_10])).

tff(c_149,plain,(
    ! [B_49,C_50] :
      ( k3_xboole_0(B_49,C_50) = C_50
      | ~ r1_tarski(C_50,B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_171,plain,(
    ! [C_52,A_53,B_54] :
      ( k3_xboole_0(C_52,k2_tarski(A_53,B_54)) = k2_tarski(A_53,B_54)
      | ~ r2_hidden(B_54,C_52)
      | ~ r2_hidden(A_53,C_52) ) ),
    inference(resolution,[status(thm)],[c_20,c_149])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    k3_xboole_0(k2_tarski('#skF_2','#skF_4'),'#skF_3') != k2_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_2','#skF_4')) != k2_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_181,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_32])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.10/1.32  
% 2.10/1.32  %Foreground sorts:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Background operators:
% 2.10/1.32  
% 2.10/1.32  
% 2.10/1.32  %Foreground operators:
% 2.10/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.32  
% 2.10/1.33  tff(f_63, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 2.10/1.33  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.10/1.33  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.33  tff(f_46, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.10/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.10/1.33  tff(c_30, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.33  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.33  tff(c_20, plain, (![A_14, B_15, C_16]: (r1_tarski(k2_tarski(A_14, B_15), C_16) | ~r2_hidden(B_15, C_16) | ~r2_hidden(A_14, C_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.33  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.33  tff(c_133, plain, (![A_46, B_47, C_48]: (r1_tarski('#skF_1'(A_46, B_47, C_48), C_48) | k3_xboole_0(B_47, C_48)=A_46 | ~r1_tarski(A_46, C_48) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.33  tff(c_10, plain, (![A_5, B_6, C_7]: (~r1_tarski('#skF_1'(A_5, B_6, C_7), A_5) | k3_xboole_0(B_6, C_7)=A_5 | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.33  tff(c_137, plain, (![B_47, C_48]: (k3_xboole_0(B_47, C_48)=C_48 | ~r1_tarski(C_48, C_48) | ~r1_tarski(C_48, B_47))), inference(resolution, [status(thm)], [c_133, c_10])).
% 2.10/1.33  tff(c_149, plain, (![B_49, C_50]: (k3_xboole_0(B_49, C_50)=C_50 | ~r1_tarski(C_50, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_137])).
% 2.10/1.33  tff(c_171, plain, (![C_52, A_53, B_54]: (k3_xboole_0(C_52, k2_tarski(A_53, B_54))=k2_tarski(A_53, B_54) | ~r2_hidden(B_54, C_52) | ~r2_hidden(A_53, C_52))), inference(resolution, [status(thm)], [c_20, c_149])).
% 2.10/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.33  tff(c_26, plain, (k3_xboole_0(k2_tarski('#skF_2', '#skF_4'), '#skF_3')!=k2_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.33  tff(c_32, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_2', '#skF_4'))!=k2_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 2.10/1.33  tff(c_181, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_171, c_32])).
% 2.10/1.33  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_181])).
% 2.10/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.33  
% 2.10/1.33  Inference rules
% 2.10/1.33  ----------------------
% 2.10/1.33  #Ref     : 0
% 2.10/1.33  #Sup     : 37
% 2.10/1.33  #Fact    : 0
% 2.10/1.33  #Define  : 0
% 2.10/1.33  #Split   : 0
% 2.10/1.33  #Chain   : 0
% 2.10/1.33  #Close   : 0
% 2.10/1.33  
% 2.10/1.33  Ordering : KBO
% 2.10/1.33  
% 2.10/1.33  Simplification rules
% 2.10/1.33  ----------------------
% 2.10/1.33  #Subsume      : 0
% 2.10/1.33  #Demod        : 10
% 2.10/1.33  #Tautology    : 21
% 2.10/1.33  #SimpNegUnit  : 0
% 2.10/1.33  #BackRed      : 0
% 2.10/1.33  
% 2.10/1.33  #Partial instantiations: 0
% 2.10/1.33  #Strategies tried      : 1
% 2.10/1.33  
% 2.10/1.33  Timing (in seconds)
% 2.10/1.33  ----------------------
% 2.10/1.33  Preprocessing        : 0.31
% 2.10/1.33  Parsing              : 0.16
% 2.10/1.33  CNF conversion       : 0.02
% 2.10/1.33  Main loop            : 0.16
% 2.10/1.33  Inferencing          : 0.06
% 2.10/1.33  Reduction            : 0.05
% 2.10/1.33  Demodulation         : 0.04
% 2.10/1.33  BG Simplification    : 0.01
% 2.10/1.33  Subsumption          : 0.03
% 2.10/1.33  Abstraction          : 0.01
% 2.10/1.33  MUC search           : 0.00
% 2.10/1.33  Cooper               : 0.00
% 2.10/1.33  Total                : 0.49
% 2.10/1.33  Index Insertion      : 0.00
% 2.10/1.33  Index Deletion       : 0.00
% 2.10/1.33  Index Matching       : 0.00
% 2.10/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
