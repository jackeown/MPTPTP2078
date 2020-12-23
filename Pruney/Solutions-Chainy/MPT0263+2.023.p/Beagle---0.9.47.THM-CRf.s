%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:16 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  42 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_102,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_106,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_48])).

tff(c_28,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [B_25,C_26] :
      ( k4_xboole_0(k2_tarski(B_25,B_25),C_26) = k1_tarski(B_25)
      | r2_hidden(B_25,C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_190,plain,(
    ! [B_55,C_56] :
      ( k4_xboole_0(k1_tarski(B_55),C_56) = k1_tarski(B_55)
      | r2_hidden(B_55,C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42])).

tff(c_474,plain,(
    ! [B_85,B_86] :
      ( k3_xboole_0(k1_tarski(B_85),B_86) = k1_tarski(B_85)
      | r2_hidden(B_85,k4_xboole_0(k1_tarski(B_85),B_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_190])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_505,plain,(
    ! [B_87,B_88] :
      ( ~ r2_hidden(B_87,B_88)
      | k3_xboole_0(k1_tarski(B_87),B_88) = k1_tarski(B_87) ) ),
    inference(resolution,[status(thm)],[c_474,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_540,plain,(
    ! [B_89,B_90] :
      ( k3_xboole_0(B_89,k1_tarski(B_90)) = k1_tarski(B_90)
      | ~ r2_hidden(B_90,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_2])).

tff(c_46,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_562,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_50])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.35  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.56/1.35  
% 2.56/1.35  %Foreground sorts:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Background operators:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Foreground operators:
% 2.56/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.56/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.56/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.56/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.56/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.56/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.35  
% 2.56/1.36  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.56/1.36  tff(f_82, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.56/1.36  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.56/1.36  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.56/1.36  tff(f_77, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.56/1.36  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.56/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.56/1.36  tff(c_102, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.56/1.36  tff(c_48, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.56/1.36  tff(c_106, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_102, c_48])).
% 2.56/1.36  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.36  tff(c_30, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.56/1.36  tff(c_42, plain, (![B_25, C_26]: (k4_xboole_0(k2_tarski(B_25, B_25), C_26)=k1_tarski(B_25) | r2_hidden(B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.36  tff(c_190, plain, (![B_55, C_56]: (k4_xboole_0(k1_tarski(B_55), C_56)=k1_tarski(B_55) | r2_hidden(B_55, C_56))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42])).
% 2.56/1.36  tff(c_474, plain, (![B_85, B_86]: (k3_xboole_0(k1_tarski(B_85), B_86)=k1_tarski(B_85) | r2_hidden(B_85, k4_xboole_0(k1_tarski(B_85), B_86)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_190])).
% 2.56/1.36  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.36  tff(c_505, plain, (![B_87, B_88]: (~r2_hidden(B_87, B_88) | k3_xboole_0(k1_tarski(B_87), B_88)=k1_tarski(B_87))), inference(resolution, [status(thm)], [c_474, c_6])).
% 2.56/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.56/1.36  tff(c_540, plain, (![B_89, B_90]: (k3_xboole_0(B_89, k1_tarski(B_90))=k1_tarski(B_90) | ~r2_hidden(B_90, B_89))), inference(superposition, [status(thm), theory('equality')], [c_505, c_2])).
% 2.56/1.36  tff(c_46, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.56/1.36  tff(c_50, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 2.56/1.36  tff(c_562, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_540, c_50])).
% 2.56/1.36  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_562])).
% 2.56/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.36  
% 2.56/1.36  Inference rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Ref     : 0
% 2.56/1.36  #Sup     : 137
% 2.56/1.36  #Fact    : 0
% 2.56/1.36  #Define  : 0
% 2.56/1.36  #Split   : 0
% 2.56/1.36  #Chain   : 0
% 2.56/1.36  #Close   : 0
% 2.56/1.36  
% 2.56/1.36  Ordering : KBO
% 2.56/1.36  
% 2.56/1.36  Simplification rules
% 2.56/1.36  ----------------------
% 2.56/1.36  #Subsume      : 9
% 2.56/1.36  #Demod        : 7
% 2.56/1.36  #Tautology    : 43
% 2.56/1.36  #SimpNegUnit  : 0
% 2.56/1.36  #BackRed      : 0
% 2.56/1.36  
% 2.56/1.36  #Partial instantiations: 0
% 2.56/1.36  #Strategies tried      : 1
% 2.56/1.36  
% 2.56/1.36  Timing (in seconds)
% 2.56/1.36  ----------------------
% 2.56/1.36  Preprocessing        : 0.30
% 2.56/1.36  Parsing              : 0.16
% 2.56/1.36  CNF conversion       : 0.02
% 2.56/1.36  Main loop            : 0.27
% 2.56/1.36  Inferencing          : 0.10
% 2.56/1.36  Reduction            : 0.08
% 2.56/1.36  Demodulation         : 0.06
% 2.56/1.36  BG Simplification    : 0.02
% 2.56/1.36  Subsumption          : 0.05
% 2.56/1.36  Abstraction          : 0.02
% 2.56/1.36  MUC search           : 0.00
% 2.56/1.36  Cooper               : 0.00
% 2.56/1.36  Total                : 0.59
% 2.56/1.36  Index Insertion      : 0.00
% 2.56/1.36  Index Deletion       : 0.00
% 2.56/1.36  Index Matching       : 0.00
% 2.56/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
