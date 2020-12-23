%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:04 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,negated_conjecture,(
    ~ ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_189,plain,(
    ! [B_41,C_42] :
      ( r2_hidden('#skF_2'(B_41,B_41,C_42),C_42)
      | k2_xboole_0(B_41,B_41) = C_42
      | r2_hidden('#skF_1'(B_41,B_41,C_42),B_41) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_219,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_2'(B_41,B_41,B_41),B_41)
      | k2_xboole_0(B_41,B_41) = B_41 ) ),
    inference(resolution,[status(thm)],[c_189,c_16])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_363,plain,(
    ! [B_51,C_52] :
      ( ~ r2_hidden('#skF_2'(B_51,B_51,C_52),B_51)
      | k2_xboole_0(B_51,B_51) = C_52
      | r2_hidden('#skF_1'(B_51,B_51,C_52),B_51) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_448,plain,(
    ! [B_56] :
      ( ~ r2_hidden('#skF_2'(B_56,B_56,B_56),B_56)
      | k2_xboole_0(B_56,B_56) = B_56 ) ),
    inference(resolution,[status(thm)],[c_363,c_12])).

tff(c_485,plain,(
    ! [B_57] : k2_xboole_0(B_57,B_57) = B_57 ),
    inference(resolution,[status(thm)],[c_219,c_448])).

tff(c_20,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_501,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_20])).

tff(c_22,plain,(
    k2_tarski('#skF_3','#skF_3') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.33  
% 2.38/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.33  %$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.33  
% 2.38/1.34  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.38/1.34  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.38/1.34  tff(f_39, negated_conjecture, ~(![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.38/1.34  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.34  tff(c_189, plain, (![B_41, C_42]: (r2_hidden('#skF_2'(B_41, B_41, C_42), C_42) | k2_xboole_0(B_41, B_41)=C_42 | r2_hidden('#skF_1'(B_41, B_41, C_42), B_41))), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 2.38/1.34  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.34  tff(c_219, plain, (![B_41]: (r2_hidden('#skF_2'(B_41, B_41, B_41), B_41) | k2_xboole_0(B_41, B_41)=B_41)), inference(resolution, [status(thm)], [c_189, c_16])).
% 2.38/1.34  tff(c_14, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.34  tff(c_363, plain, (![B_51, C_52]: (~r2_hidden('#skF_2'(B_51, B_51, C_52), B_51) | k2_xboole_0(B_51, B_51)=C_52 | r2_hidden('#skF_1'(B_51, B_51, C_52), B_51))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 2.38/1.34  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.34  tff(c_448, plain, (![B_56]: (~r2_hidden('#skF_2'(B_56, B_56, B_56), B_56) | k2_xboole_0(B_56, B_56)=B_56)), inference(resolution, [status(thm)], [c_363, c_12])).
% 2.38/1.34  tff(c_485, plain, (![B_57]: (k2_xboole_0(B_57, B_57)=B_57)), inference(resolution, [status(thm)], [c_219, c_448])).
% 2.38/1.34  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.34  tff(c_501, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_485, c_20])).
% 2.38/1.34  tff(c_22, plain, (k2_tarski('#skF_3', '#skF_3')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.34  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_22])).
% 2.38/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  Inference rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Ref     : 0
% 2.38/1.34  #Sup     : 93
% 2.38/1.34  #Fact    : 6
% 2.38/1.34  #Define  : 0
% 2.38/1.34  #Split   : 0
% 2.38/1.34  #Chain   : 0
% 2.38/1.34  #Close   : 0
% 2.38/1.34  
% 2.38/1.34  Ordering : KBO
% 2.38/1.34  
% 2.38/1.34  Simplification rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Subsume      : 13
% 2.38/1.34  #Demod        : 5
% 2.38/1.34  #Tautology    : 18
% 2.38/1.34  #SimpNegUnit  : 0
% 2.38/1.34  #BackRed      : 3
% 2.38/1.34  
% 2.38/1.34  #Partial instantiations: 0
% 2.38/1.34  #Strategies tried      : 1
% 2.38/1.34  
% 2.38/1.34  Timing (in seconds)
% 2.38/1.34  ----------------------
% 2.38/1.35  Preprocessing        : 0.29
% 2.38/1.35  Parsing              : 0.15
% 2.38/1.35  CNF conversion       : 0.02
% 2.38/1.35  Main loop            : 0.27
% 2.38/1.35  Inferencing          : 0.11
% 2.38/1.35  Reduction            : 0.06
% 2.38/1.35  Demodulation         : 0.04
% 2.38/1.35  BG Simplification    : 0.02
% 2.38/1.35  Subsumption          : 0.07
% 2.38/1.35  Abstraction          : 0.02
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.35  Cooper               : 0.00
% 2.38/1.35  Total                : 0.58
% 2.38/1.35  Index Insertion      : 0.00
% 2.38/1.35  Index Deletion       : 0.00
% 2.38/1.35  Index Matching       : 0.00
% 2.38/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
