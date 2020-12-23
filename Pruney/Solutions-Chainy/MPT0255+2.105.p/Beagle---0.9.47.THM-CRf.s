%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:52 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_20,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_121])).

tff(c_254,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [A_13,C_75] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_75,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_254])).

tff(c_259,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_257])).

tff(c_58,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_86,plain,(
    ! [A_52,B_53] :
      ( k1_xboole_0 = A_52
      | k2_xboole_0(A_52,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_86])).

tff(c_24,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_24])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.10/1.30  
% 2.10/1.30  %Foreground sorts:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Background operators:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Foreground operators:
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.30  
% 2.10/1.31  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.10/1.31  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.31  tff(f_90, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.10/1.31  tff(f_53, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.10/1.31  tff(f_66, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.31  tff(c_20, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.31  tff(c_121, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.31  tff(c_129, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_121])).
% 2.10/1.31  tff(c_254, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.31  tff(c_257, plain, (![A_13, C_75]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_129, c_254])).
% 2.10/1.31  tff(c_259, plain, (![C_75]: (~r2_hidden(C_75, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_257])).
% 2.10/1.31  tff(c_58, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.10/1.31  tff(c_86, plain, (![A_52, B_53]: (k1_xboole_0=A_52 | k2_xboole_0(A_52, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.31  tff(c_90, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_58, c_86])).
% 2.10/1.31  tff(c_24, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.31  tff(c_98, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_24])).
% 2.10/1.31  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_98])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 50
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 1
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 1
% 2.10/1.31  #Demod        : 7
% 2.10/1.31  #Tautology    : 32
% 2.10/1.31  #SimpNegUnit  : 2
% 2.10/1.31  #BackRed      : 3
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.32
% 2.10/1.31  Parsing              : 0.17
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.17
% 2.10/1.31  Inferencing          : 0.05
% 2.10/1.31  Reduction            : 0.06
% 2.10/1.31  Demodulation         : 0.04
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.03
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.52
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
