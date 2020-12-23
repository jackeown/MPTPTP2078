%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:14 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,(
    ! [D_13,B_14] : r2_hidden(D_13,k2_tarski(D_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_43])).

tff(c_26,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_29,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden(A_18,B_19)
      | ~ r1_xboole_0(k1_tarski(A_18),B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_29,c_53])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.09  
% 1.58/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.09  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.58/1.09  
% 1.58/1.09  %Foreground sorts:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Background operators:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Foreground operators:
% 1.58/1.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.58/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.58/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.09  
% 1.58/1.10  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.58/1.10  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.58/1.10  tff(f_49, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.58/1.10  tff(f_43, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.58/1.10  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.58/1.10  tff(c_43, plain, (![D_13, B_14]: (r2_hidden(D_13, k2_tarski(D_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.10  tff(c_46, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_43])).
% 1.58/1.10  tff(c_26, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.58/1.10  tff(c_28, plain, (r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.58/1.10  tff(c_29, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 1.58/1.10  tff(c_53, plain, (![A_18, B_19]: (~r2_hidden(A_18, B_19) | ~r1_xboole_0(k1_tarski(A_18), B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.10  tff(c_56, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_29, c_53])).
% 1.58/1.10  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 1.58/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.10  
% 1.58/1.10  Inference rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Ref     : 0
% 1.58/1.10  #Sup     : 7
% 1.58/1.10  #Fact    : 0
% 1.58/1.10  #Define  : 0
% 1.58/1.10  #Split   : 0
% 1.58/1.10  #Chain   : 0
% 1.58/1.10  #Close   : 0
% 1.58/1.10  
% 1.58/1.10  Ordering : KBO
% 1.58/1.10  
% 1.58/1.10  Simplification rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Subsume      : 0
% 1.58/1.10  #Demod        : 3
% 1.58/1.10  #Tautology    : 5
% 1.58/1.10  #SimpNegUnit  : 0
% 1.58/1.10  #BackRed      : 0
% 1.58/1.10  
% 1.58/1.10  #Partial instantiations: 0
% 1.58/1.10  #Strategies tried      : 1
% 1.58/1.10  
% 1.58/1.10  Timing (in seconds)
% 1.58/1.10  ----------------------
% 1.58/1.10  Preprocessing        : 0.27
% 1.58/1.10  Parsing              : 0.13
% 1.58/1.10  CNF conversion       : 0.02
% 1.58/1.10  Main loop            : 0.07
% 1.58/1.10  Inferencing          : 0.02
% 1.58/1.10  Reduction            : 0.03
% 1.58/1.10  Demodulation         : 0.02
% 1.58/1.10  BG Simplification    : 0.01
% 1.58/1.10  Subsumption          : 0.01
% 1.58/1.10  Abstraction          : 0.00
% 1.58/1.10  MUC search           : 0.00
% 1.58/1.10  Cooper               : 0.00
% 1.58/1.10  Total                : 0.36
% 1.58/1.10  Index Insertion      : 0.00
% 1.58/1.10  Index Deletion       : 0.00
% 1.58/1.10  Index Matching       : 0.00
% 1.58/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
