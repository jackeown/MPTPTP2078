%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:46 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_14,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_enumset1(A_14,A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_33,B_34,C_35,D_36] : k2_xboole_0(k2_tarski(A_33,B_34),k2_tarski(C_35,D_36)) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(A_22,C_23)
      | ~ r1_tarski(k2_xboole_0(A_22,B_24),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_22,B_24] : r1_tarski(A_22,k2_xboole_0(A_22,B_24)) ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_129,plain,(
    ! [A_42,B_43,C_44,D_45] : r1_tarski(k2_tarski(A_42,B_43),k2_enumset1(A_42,B_43,C_44,D_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_51])).

tff(c_136,plain,(
    ! [A_14,B_15] : r1_tarski(k2_tarski(A_14,A_14),k2_tarski(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_129])).

tff(c_142,plain,(
    ! [A_14,B_15] : r1_tarski(k1_tarski(A_14),k2_tarski(A_14,B_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_18,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:53:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.13  
% 1.79/1.13  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.79/1.13  tff(f_47, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 1.79/1.13  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.79/1.13  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.79/1.13  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.79/1.13  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.79/1.13  tff(c_14, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.13  tff(c_16, plain, (![A_14, B_15]: (k2_enumset1(A_14, A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.13  tff(c_80, plain, (![A_33, B_34, C_35, D_36]: (k2_xboole_0(k2_tarski(A_33, B_34), k2_tarski(C_35, D_36))=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.79/1.13  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.13  tff(c_46, plain, (![A_22, C_23, B_24]: (r1_tarski(A_22, C_23) | ~r1_tarski(k2_xboole_0(A_22, B_24), C_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.13  tff(c_51, plain, (![A_22, B_24]: (r1_tarski(A_22, k2_xboole_0(A_22, B_24)))), inference(resolution, [status(thm)], [c_6, c_46])).
% 1.79/1.13  tff(c_129, plain, (![A_42, B_43, C_44, D_45]: (r1_tarski(k2_tarski(A_42, B_43), k2_enumset1(A_42, B_43, C_44, D_45)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_51])).
% 1.79/1.13  tff(c_136, plain, (![A_14, B_15]: (r1_tarski(k2_tarski(A_14, A_14), k2_tarski(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_129])).
% 1.79/1.13  tff(c_142, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), k2_tarski(A_14, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 1.79/1.13  tff(c_18, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.13  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_18])).
% 1.79/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.13  
% 1.79/1.13  Inference rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Ref     : 0
% 1.79/1.13  #Sup     : 30
% 1.79/1.13  #Fact    : 0
% 1.79/1.13  #Define  : 0
% 1.79/1.13  #Split   : 0
% 1.79/1.13  #Chain   : 0
% 1.79/1.13  #Close   : 0
% 1.79/1.13  
% 1.79/1.13  Ordering : KBO
% 1.79/1.13  
% 1.79/1.13  Simplification rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Subsume      : 0
% 1.79/1.13  #Demod        : 5
% 1.79/1.13  #Tautology    : 9
% 1.79/1.13  #SimpNegUnit  : 0
% 1.79/1.13  #BackRed      : 1
% 1.79/1.13  
% 1.79/1.13  #Partial instantiations: 0
% 1.79/1.13  #Strategies tried      : 1
% 1.79/1.13  
% 1.79/1.13  Timing (in seconds)
% 1.79/1.13  ----------------------
% 1.79/1.14  Preprocessing        : 0.27
% 1.79/1.14  Parsing              : 0.14
% 1.79/1.14  CNF conversion       : 0.02
% 1.79/1.14  Main loop            : 0.12
% 1.79/1.14  Inferencing          : 0.05
% 1.79/1.14  Reduction            : 0.04
% 1.79/1.14  Demodulation         : 0.03
% 1.79/1.14  BG Simplification    : 0.01
% 1.79/1.14  Subsumption          : 0.02
% 1.79/1.14  Abstraction          : 0.01
% 1.79/1.14  MUC search           : 0.00
% 1.79/1.14  Cooper               : 0.00
% 1.79/1.14  Total                : 0.41
% 1.79/1.14  Index Insertion      : 0.00
% 1.79/1.14  Index Deletion       : 0.00
% 1.79/1.14  Index Matching       : 0.00
% 1.79/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
