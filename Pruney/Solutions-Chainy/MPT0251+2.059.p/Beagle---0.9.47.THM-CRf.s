%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  48 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_232,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(k2_tarski(A_71,B_72),C_73)
      | ~ r2_hidden(B_72,C_73)
      | ~ r2_hidden(A_71,C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_254,plain,(
    ! [A_74,C_75] :
      ( r1_tarski(k1_tarski(A_74),C_75)
      | ~ r2_hidden(A_74,C_75)
      | ~ r2_hidden(A_74,C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_232])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_263,plain,(
    ! [A_76,C_77] :
      ( k2_xboole_0(k1_tarski(A_76),C_77) = C_77
      | ~ r2_hidden(A_76,C_77) ) ),
    inference(resolution,[status(thm)],[c_254,c_35])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_123,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(B_53,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_79])).

tff(c_24,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_129,plain,(
    ! [B_53,A_52] : k2_xboole_0(B_53,A_52) = k2_xboole_0(A_52,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_24])).

tff(c_302,plain,(
    ! [C_78,A_79] :
      ( k2_xboole_0(C_78,k1_tarski(A_79)) = C_78
      | ~ r2_hidden(A_79,C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_129])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_158,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_32])).

tff(c_312,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_158])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.22  
% 2.11/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.11/1.23  
% 2.11/1.23  %Foreground sorts:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Background operators:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Foreground operators:
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.23  
% 2.14/1.24  tff(f_62, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.14/1.24  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.24  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.24  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.14/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.14/1.24  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.14/1.24  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.14/1.24  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.24  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.24  tff(c_232, plain, (![A_71, B_72, C_73]: (r1_tarski(k2_tarski(A_71, B_72), C_73) | ~r2_hidden(B_72, C_73) | ~r2_hidden(A_71, C_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.24  tff(c_254, plain, (![A_74, C_75]: (r1_tarski(k1_tarski(A_74), C_75) | ~r2_hidden(A_74, C_75) | ~r2_hidden(A_74, C_75))), inference(superposition, [status(thm), theory('equality')], [c_10, c_232])).
% 2.14/1.24  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.24  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.24  tff(c_35, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.14/1.24  tff(c_263, plain, (![A_76, C_77]: (k2_xboole_0(k1_tarski(A_76), C_77)=C_77 | ~r2_hidden(A_76, C_77))), inference(resolution, [status(thm)], [c_254, c_35])).
% 2.14/1.24  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.24  tff(c_79, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.24  tff(c_123, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(B_53, A_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_79])).
% 2.14/1.24  tff(c_24, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.24  tff(c_129, plain, (![B_53, A_52]: (k2_xboole_0(B_53, A_52)=k2_xboole_0(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_123, c_24])).
% 2.14/1.24  tff(c_302, plain, (![C_78, A_79]: (k2_xboole_0(C_78, k1_tarski(A_79))=C_78 | ~r2_hidden(A_79, C_78))), inference(superposition, [status(thm), theory('equality')], [c_263, c_129])).
% 2.14/1.24  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.24  tff(c_158, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_32])).
% 2.14/1.24  tff(c_312, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_302, c_158])).
% 2.14/1.24  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_312])).
% 2.14/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  Inference rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Ref     : 0
% 2.14/1.24  #Sup     : 77
% 2.14/1.24  #Fact    : 0
% 2.14/1.24  #Define  : 0
% 2.14/1.24  #Split   : 0
% 2.14/1.24  #Chain   : 0
% 2.14/1.24  #Close   : 0
% 2.14/1.24  
% 2.14/1.24  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 9
% 2.14/1.24  #Demod        : 6
% 2.14/1.24  #Tautology    : 43
% 2.14/1.24  #SimpNegUnit  : 0
% 2.14/1.24  #BackRed      : 1
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.24  Preprocessing        : 0.30
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.18
% 2.14/1.24  Inferencing          : 0.07
% 2.14/1.24  Reduction            : 0.06
% 2.14/1.24  Demodulation         : 0.05
% 2.14/1.24  BG Simplification    : 0.02
% 2.14/1.24  Subsumption          : 0.03
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.51
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
