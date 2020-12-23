%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:08 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_89,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(k1_tarski(A_46),B_47) = k1_xboole_0
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_28,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_28])).

tff(c_14,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_xboole_0(k2_tarski(A_48,C_49),B_50)
      | r2_hidden(C_49,B_50)
      | r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_188,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_193,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(k1_tarski(A_53),B_54) = k1_tarski(A_53)
      | r2_hidden(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_188,c_10])).

tff(c_26,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_205,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_26])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.83/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.17  
% 1.91/1.18  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.91/1.18  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.91/1.18  tff(f_62, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.91/1.18  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.18  tff(f_57, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.91/1.18  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.91/1.18  tff(c_89, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.18  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.18  tff(c_160, plain, (![A_46, B_47]: (k4_xboole_0(k1_tarski(A_46), B_47)=k1_xboole_0 | ~r2_hidden(A_46, B_47))), inference(resolution, [status(thm)], [c_89, c_6])).
% 1.91/1.18  tff(c_28, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.18  tff(c_178, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_28])).
% 1.91/1.18  tff(c_14, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.18  tff(c_180, plain, (![A_48, C_49, B_50]: (r1_xboole_0(k2_tarski(A_48, C_49), B_50) | r2_hidden(C_49, B_50) | r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.18  tff(c_188, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52) | r2_hidden(A_51, B_52))), inference(superposition, [status(thm), theory('equality')], [c_14, c_180])).
% 1.91/1.18  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.18  tff(c_193, plain, (![A_53, B_54]: (k4_xboole_0(k1_tarski(A_53), B_54)=k1_tarski(A_53) | r2_hidden(A_53, B_54))), inference(resolution, [status(thm)], [c_188, c_10])).
% 1.91/1.18  tff(c_26, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.18  tff(c_205, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_26])).
% 1.91/1.18  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_205])).
% 1.91/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  Inference rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Ref     : 0
% 1.91/1.18  #Sup     : 44
% 1.91/1.18  #Fact    : 0
% 1.91/1.18  #Define  : 0
% 1.91/1.18  #Split   : 0
% 1.91/1.18  #Chain   : 0
% 1.91/1.18  #Close   : 0
% 1.91/1.18  
% 1.91/1.18  Ordering : KBO
% 1.91/1.18  
% 1.91/1.18  Simplification rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Subsume      : 1
% 1.91/1.18  #Demod        : 3
% 1.91/1.18  #Tautology    : 31
% 1.91/1.18  #SimpNegUnit  : 1
% 1.91/1.18  #BackRed      : 0
% 1.91/1.18  
% 1.91/1.18  #Partial instantiations: 0
% 1.91/1.18  #Strategies tried      : 1
% 1.91/1.18  
% 1.91/1.18  Timing (in seconds)
% 1.91/1.18  ----------------------
% 1.91/1.18  Preprocessing        : 0.29
% 1.91/1.18  Parsing              : 0.15
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.14
% 1.91/1.18  Inferencing          : 0.06
% 1.91/1.18  Reduction            : 0.04
% 1.91/1.18  Demodulation         : 0.03
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.02
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.45
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
