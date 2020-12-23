%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:53 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_43,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_4])).

tff(c_107,plain,(
    ! [B_36,C_37,A_38] :
      ( ~ r2_hidden(B_36,C_37)
      | k4_xboole_0(k2_tarski(A_38,B_36),C_37) = k1_tarski(A_38)
      | r2_hidden(A_38,C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_119,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_32])).

tff(c_131,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_119])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [D_21,B_22,A_23] :
      ( D_21 = B_22
      | D_21 = A_23
      | ~ r2_hidden(D_21,k2_tarski(A_23,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    ! [D_21,A_7] :
      ( D_21 = A_7
      | D_21 = A_7
      | ~ r2_hidden(D_21,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_135,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_131,c_70])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.18  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.78/1.18  
% 1.78/1.18  %Foreground sorts:
% 1.78/1.18  
% 1.78/1.18  
% 1.78/1.18  %Background operators:
% 1.78/1.18  
% 1.78/1.18  
% 1.78/1.18  %Foreground operators:
% 1.78/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.18  
% 1.78/1.19  tff(f_53, negated_conjecture, ~(![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 1.78/1.19  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.78/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.78/1.19  tff(f_47, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.78/1.19  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.78/1.19  tff(c_37, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.78/1.19  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.78/1.19  tff(c_43, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_4])).
% 1.78/1.19  tff(c_107, plain, (![B_36, C_37, A_38]: (~r2_hidden(B_36, C_37) | k4_xboole_0(k2_tarski(A_38, B_36), C_37)=k1_tarski(A_38) | r2_hidden(A_38, C_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.19  tff(c_32, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.78/1.19  tff(c_119, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_32])).
% 1.78/1.19  tff(c_131, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_119])).
% 1.78/1.19  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.78/1.19  tff(c_64, plain, (![D_21, B_22, A_23]: (D_21=B_22 | D_21=A_23 | ~r2_hidden(D_21, k2_tarski(A_23, B_22)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.78/1.19  tff(c_70, plain, (![D_21, A_7]: (D_21=A_7 | D_21=A_7 | ~r2_hidden(D_21, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_64])).
% 1.78/1.19  tff(c_135, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_131, c_70])).
% 1.78/1.19  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_135])).
% 1.78/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  Inference rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Ref     : 0
% 1.78/1.19  #Sup     : 22
% 1.78/1.19  #Fact    : 0
% 1.78/1.19  #Define  : 0
% 1.78/1.19  #Split   : 0
% 1.78/1.19  #Chain   : 0
% 1.78/1.19  #Close   : 0
% 1.78/1.19  
% 1.78/1.19  Ordering : KBO
% 1.78/1.19  
% 1.78/1.19  Simplification rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Subsume      : 1
% 1.78/1.19  #Demod        : 3
% 1.78/1.19  #Tautology    : 16
% 1.78/1.19  #SimpNegUnit  : 1
% 1.78/1.19  #BackRed      : 0
% 1.78/1.19  
% 1.78/1.19  #Partial instantiations: 0
% 1.78/1.19  #Strategies tried      : 1
% 1.78/1.19  
% 1.78/1.19  Timing (in seconds)
% 1.78/1.19  ----------------------
% 1.78/1.19  Preprocessing        : 0.29
% 1.78/1.19  Parsing              : 0.15
% 1.78/1.19  CNF conversion       : 0.02
% 1.78/1.19  Main loop            : 0.12
% 1.78/1.19  Inferencing          : 0.04
% 1.78/1.19  Reduction            : 0.04
% 1.78/1.19  Demodulation         : 0.03
% 1.78/1.19  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.03
% 1.78/1.19  Abstraction          : 0.01
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.43
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
