%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:13 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   36 (  59 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  98 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,B)
          & ~ r2_hidden(C,B)
          & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,D)
        & r1_xboole_0(B,D)
        & r1_xboole_0(C,D) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),B_12)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(A_1,B_2),C_3),D_4)
      | ~ r1_xboole_0(C_3,D_4)
      | ~ r1_xboole_0(B_2,D_4)
      | ~ r1_xboole_0(A_1,D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r1_xboole_0(k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)),D_30)
      | ~ r1_xboole_0(C_29,D_30)
      | ~ r1_xboole_0(B_28,D_30)
      | ~ r1_xboole_0(A_27,D_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2])).

tff(c_288,plain,(
    ! [A_41,A_42,B_43,D_44] :
      ( r1_xboole_0(k2_xboole_0(A_41,k2_tarski(A_42,B_43)),D_44)
      | ~ r1_xboole_0(k1_tarski(B_43),D_44)
      | ~ r1_xboole_0(k1_tarski(A_42),D_44)
      | ~ r1_xboole_0(A_41,D_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_443,plain,(
    ! [A_55,A_56,D_57] :
      ( r1_xboole_0(k2_xboole_0(A_55,k1_tarski(A_56)),D_57)
      | ~ r1_xboole_0(k1_tarski(A_56),D_57)
      | ~ r1_xboole_0(k1_tarski(A_56),D_57)
      | ~ r1_xboole_0(A_55,D_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_288])).

tff(c_460,plain,(
    ! [A_58,B_59,D_60] :
      ( r1_xboole_0(k2_tarski(A_58,B_59),D_60)
      | ~ r1_xboole_0(k1_tarski(B_59),D_60)
      | ~ r1_xboole_0(k1_tarski(B_59),D_60)
      | ~ r1_xboole_0(k1_tarski(A_58),D_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_443])).

tff(c_12,plain,(
    ~ r1_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_467,plain,
    ( ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_2')
    | ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_460,c_12])).

tff(c_554,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_557,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_554])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_557])).

tff(c_562,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_566,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_562])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.57/1.37  
% 2.57/1.37  %Foreground sorts:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Background operators:
% 2.57/1.37  
% 2.57/1.37  
% 2.57/1.37  %Foreground operators:
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.37  
% 2.57/1.38  tff(f_55, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.57/1.38  tff(f_44, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.57/1.38  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.57/1.38  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.57/1.38  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.57/1.38  tff(f_33, axiom, (![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_xboole_1)).
% 2.57/1.38  tff(c_14, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.38  tff(c_10, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), B_12) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.38  tff(c_16, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.38  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.38  tff(c_8, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.38  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.38  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r1_xboole_0(k2_xboole_0(k2_xboole_0(A_1, B_2), C_3), D_4) | ~r1_xboole_0(C_3, D_4) | ~r1_xboole_0(B_2, D_4) | ~r1_xboole_0(A_1, D_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.38  tff(c_96, plain, (![A_27, B_28, C_29, D_30]: (r1_xboole_0(k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)), D_30) | ~r1_xboole_0(C_29, D_30) | ~r1_xboole_0(B_28, D_30) | ~r1_xboole_0(A_27, D_30))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2])).
% 2.57/1.38  tff(c_288, plain, (![A_41, A_42, B_43, D_44]: (r1_xboole_0(k2_xboole_0(A_41, k2_tarski(A_42, B_43)), D_44) | ~r1_xboole_0(k1_tarski(B_43), D_44) | ~r1_xboole_0(k1_tarski(A_42), D_44) | ~r1_xboole_0(A_41, D_44))), inference(superposition, [status(thm), theory('equality')], [c_6, c_96])).
% 2.57/1.38  tff(c_443, plain, (![A_55, A_56, D_57]: (r1_xboole_0(k2_xboole_0(A_55, k1_tarski(A_56)), D_57) | ~r1_xboole_0(k1_tarski(A_56), D_57) | ~r1_xboole_0(k1_tarski(A_56), D_57) | ~r1_xboole_0(A_55, D_57))), inference(superposition, [status(thm), theory('equality')], [c_8, c_288])).
% 2.57/1.38  tff(c_460, plain, (![A_58, B_59, D_60]: (r1_xboole_0(k2_tarski(A_58, B_59), D_60) | ~r1_xboole_0(k1_tarski(B_59), D_60) | ~r1_xboole_0(k1_tarski(B_59), D_60) | ~r1_xboole_0(k1_tarski(A_58), D_60))), inference(superposition, [status(thm), theory('equality')], [c_6, c_443])).
% 2.57/1.38  tff(c_12, plain, (~r1_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.38  tff(c_467, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_2') | ~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_460, c_12])).
% 2.57/1.38  tff(c_554, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_467])).
% 2.57/1.38  tff(c_557, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_554])).
% 2.57/1.38  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_557])).
% 2.57/1.38  tff(c_562, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_467])).
% 2.57/1.38  tff(c_566, plain, (r2_hidden('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_562])).
% 2.57/1.38  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_566])).
% 2.57/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  Inference rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Ref     : 0
% 2.57/1.38  #Sup     : 141
% 2.57/1.38  #Fact    : 0
% 2.57/1.38  #Define  : 0
% 2.57/1.38  #Split   : 1
% 2.57/1.38  #Chain   : 0
% 2.57/1.38  #Close   : 0
% 2.57/1.38  
% 2.57/1.38  Ordering : KBO
% 2.57/1.38  
% 2.57/1.38  Simplification rules
% 2.57/1.38  ----------------------
% 2.57/1.38  #Subsume      : 5
% 2.57/1.38  #Demod        : 121
% 2.57/1.38  #Tautology    : 75
% 2.57/1.38  #SimpNegUnit  : 2
% 2.57/1.38  #BackRed      : 0
% 2.57/1.38  
% 2.57/1.38  #Partial instantiations: 0
% 2.57/1.38  #Strategies tried      : 1
% 2.57/1.38  
% 2.57/1.38  Timing (in seconds)
% 2.57/1.38  ----------------------
% 2.57/1.39  Preprocessing        : 0.26
% 2.57/1.39  Parsing              : 0.14
% 2.57/1.39  CNF conversion       : 0.02
% 2.57/1.39  Main loop            : 0.32
% 2.57/1.39  Inferencing          : 0.12
% 2.57/1.39  Reduction            : 0.11
% 2.57/1.39  Demodulation         : 0.09
% 2.57/1.39  BG Simplification    : 0.02
% 2.57/1.39  Subsumption          : 0.05
% 2.57/1.39  Abstraction          : 0.02
% 2.57/1.39  MUC search           : 0.00
% 2.57/1.39  Cooper               : 0.00
% 2.57/1.39  Total                : 0.61
% 2.57/1.39  Index Insertion      : 0.00
% 2.57/1.39  Index Deletion       : 0.00
% 2.57/1.39  Index Matching       : 0.00
% 2.57/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
