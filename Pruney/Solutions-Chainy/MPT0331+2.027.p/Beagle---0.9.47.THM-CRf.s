%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:48 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   23 (  33 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_16,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,k1_tarski(B_9)) = A_8
      | r2_hidden(B_9,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k4_xboole_0(A_20,B_21),C_22) = k4_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [A_25,B_26,C_27] :
      ( k4_xboole_0(A_25,k2_xboole_0(k1_tarski(B_26),C_27)) = k4_xboole_0(A_25,C_27)
      | r2_hidden(B_26,A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_78])).

tff(c_145,plain,(
    ! [A_28,A_29,B_30] :
      ( k4_xboole_0(A_28,k2_tarski(A_29,B_30)) = k4_xboole_0(A_28,k1_tarski(B_30))
      | r2_hidden(A_29,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_14,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_158,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3'
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_14])).

tff(c_169,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_158])).

tff(c_174,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_169])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:25:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.93/1.26  
% 1.93/1.26  %Foreground sorts:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Background operators:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Foreground operators:
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.26  
% 1.93/1.27  tff(f_50, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.93/1.27  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.93/1.27  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.93/1.27  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.93/1.27  tff(c_16, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.27  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k1_tarski(B_9))=A_8 | r2_hidden(B_9, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.27  tff(c_18, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.27  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.27  tff(c_78, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k4_xboole_0(A_20, B_21), C_22)=k4_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.27  tff(c_119, plain, (![A_25, B_26, C_27]: (k4_xboole_0(A_25, k2_xboole_0(k1_tarski(B_26), C_27))=k4_xboole_0(A_25, C_27) | r2_hidden(B_26, A_25))), inference(superposition, [status(thm), theory('equality')], [c_12, c_78])).
% 1.93/1.27  tff(c_145, plain, (![A_28, A_29, B_30]: (k4_xboole_0(A_28, k2_tarski(A_29, B_30))=k4_xboole_0(A_28, k1_tarski(B_30)) | r2_hidden(A_29, A_28))), inference(superposition, [status(thm), theory('equality')], [c_4, c_119])).
% 1.93/1.27  tff(c_14, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.27  tff(c_158, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3' | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_14])).
% 1.93/1.27  tff(c_169, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_158])).
% 1.93/1.27  tff(c_174, plain, (r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_169])).
% 1.93/1.27  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_174])).
% 1.93/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  Inference rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Ref     : 0
% 1.93/1.27  #Sup     : 35
% 1.93/1.27  #Fact    : 0
% 1.93/1.27  #Define  : 0
% 1.93/1.27  #Split   : 0
% 1.93/1.27  #Chain   : 0
% 1.93/1.27  #Close   : 0
% 1.93/1.27  
% 1.93/1.27  Ordering : KBO
% 1.93/1.27  
% 1.93/1.27  Simplification rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Subsume      : 0
% 1.93/1.27  #Demod        : 10
% 1.93/1.27  #Tautology    : 17
% 1.93/1.27  #SimpNegUnit  : 2
% 1.93/1.27  #BackRed      : 0
% 1.93/1.27  
% 1.93/1.27  #Partial instantiations: 0
% 1.93/1.27  #Strategies tried      : 1
% 1.93/1.27  
% 1.93/1.27  Timing (in seconds)
% 1.93/1.27  ----------------------
% 1.93/1.28  Preprocessing        : 0.34
% 1.93/1.28  Parsing              : 0.18
% 1.93/1.28  CNF conversion       : 0.02
% 1.93/1.28  Main loop            : 0.19
% 1.93/1.28  Inferencing          : 0.09
% 1.93/1.28  Reduction            : 0.05
% 1.93/1.28  Demodulation         : 0.04
% 1.93/1.28  BG Simplification    : 0.01
% 1.93/1.28  Subsumption          : 0.03
% 1.93/1.28  Abstraction          : 0.01
% 1.93/1.28  MUC search           : 0.00
% 1.93/1.28  Cooper               : 0.00
% 1.93/1.28  Total                : 0.55
% 1.93/1.28  Index Insertion      : 0.00
% 1.93/1.28  Index Deletion       : 0.00
% 1.93/1.28  Index Matching       : 0.00
% 1.93/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
