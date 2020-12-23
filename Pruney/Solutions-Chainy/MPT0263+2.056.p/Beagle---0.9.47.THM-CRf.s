%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:21 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   31 (  43 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  48 expanded)
%              Number of equality atoms :   12 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(k1_tarski(A_5),B_6) = k1_xboole_0
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(k1_tarski(A_5),k1_xboole_0) = k3_xboole_0(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_166,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(k1_tarski(A_22),B_23) = k1_tarski(A_22)
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_14,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_182,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_14])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_184,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_xboole_0(k2_tarski(A_24,C_25),B_26)
      | r2_hidden(C_25,B_26)
      | r2_hidden(A_24,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_184])).

tff(c_16,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_197,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_194,c_16])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_182,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:48:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.85/1.19  
% 1.85/1.19  %Foreground sorts:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Background operators:
% 1.85/1.19  
% 1.85/1.19  
% 1.85/1.19  %Foreground operators:
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.19  
% 1.91/1.20  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.91/1.20  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.91/1.20  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/1.20  tff(f_50, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.91/1.20  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.20  tff(f_45, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 1.91/1.20  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.20  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(k1_tarski(A_5), B_6)=k1_xboole_0 | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.20  tff(c_67, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.20  tff(c_90, plain, (![A_5, B_6]: (k4_xboole_0(k1_tarski(A_5), k1_xboole_0)=k3_xboole_0(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 1.91/1.20  tff(c_166, plain, (![A_22, B_23]: (k3_xboole_0(k1_tarski(A_22), B_23)=k1_tarski(A_22) | ~r2_hidden(A_22, B_23))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_90])).
% 1.91/1.20  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.20  tff(c_182, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_166, c_14])).
% 1.91/1.20  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.20  tff(c_184, plain, (![A_24, C_25, B_26]: (r1_xboole_0(k2_tarski(A_24, C_25), B_26) | r2_hidden(C_25, B_26) | r2_hidden(A_24, B_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.20  tff(c_194, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30) | r2_hidden(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_6, c_184])).
% 1.91/1.20  tff(c_16, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.20  tff(c_197, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_194, c_16])).
% 1.91/1.20  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_182, c_197])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 44
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 0
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 2
% 1.91/1.20  #Demod        : 5
% 1.91/1.20  #Tautology    : 21
% 1.91/1.20  #SimpNegUnit  : 1
% 1.91/1.20  #BackRed      : 0
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.28
% 1.91/1.20  Parsing              : 0.14
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.15
% 1.91/1.20  Inferencing          : 0.07
% 1.91/1.21  Reduction            : 0.04
% 1.91/1.21  Demodulation         : 0.03
% 1.91/1.21  BG Simplification    : 0.01
% 1.91/1.21  Subsumption          : 0.02
% 1.91/1.21  Abstraction          : 0.01
% 1.91/1.21  MUC search           : 0.00
% 1.91/1.21  Cooper               : 0.00
% 1.91/1.21  Total                : 0.46
% 1.91/1.21  Index Insertion      : 0.00
% 1.91/1.21  Index Deletion       : 0.00
% 1.91/1.21  Index Matching       : 0.00
% 1.91/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
