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
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   45 (  47 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  42 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_379,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k2_tarski(A_73,B_74),C_75)
      | ~ r2_hidden(B_74,C_75)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_415,plain,(
    ! [A_79,C_80] :
      ( r1_tarski(k1_tarski(A_79),C_80)
      | ~ r2_hidden(A_79,C_80)
      | ~ r2_hidden(A_79,C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_379])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_424,plain,(
    ! [A_81,C_82] :
      ( k4_xboole_0(k1_tarski(A_81),C_82) = k1_xboole_0
      | ~ r2_hidden(A_81,C_82) ) ),
    inference(resolution,[status(thm)],[c_415,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_437,plain,(
    ! [C_82,A_81] :
      ( k2_xboole_0(C_82,k1_tarski(A_81)) = k2_xboole_0(C_82,k1_xboole_0)
      | ~ r2_hidden(A_81,C_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_10])).

tff(c_454,plain,(
    ! [C_84,A_85] :
      ( k2_xboole_0(C_84,k1_tarski(A_85)) = C_84
      | ~ r2_hidden(A_85,C_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_437])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    ! [B_38,A_39] : k3_tarski(k2_tarski(B_38,A_39)) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_94])).

tff(c_22,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_22])).

tff(c_30,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_160,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_30])).

tff(c_460,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_160])).

tff(c_498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.30  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.13/1.30  
% 2.13/1.30  %Foreground sorts:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Background operators:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Foreground operators:
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.30  
% 2.13/1.31  tff(f_58, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.13/1.31  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.13/1.31  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.13/1.31  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.13/1.31  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.13/1.31  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.13/1.31  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.13/1.31  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.13/1.31  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.31  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.31  tff(c_14, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.31  tff(c_379, plain, (![A_73, B_74, C_75]: (r1_tarski(k2_tarski(A_73, B_74), C_75) | ~r2_hidden(B_74, C_75) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.31  tff(c_415, plain, (![A_79, C_80]: (r1_tarski(k1_tarski(A_79), C_80) | ~r2_hidden(A_79, C_80) | ~r2_hidden(A_79, C_80))), inference(superposition, [status(thm), theory('equality')], [c_14, c_379])).
% 2.13/1.31  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.31  tff(c_424, plain, (![A_81, C_82]: (k4_xboole_0(k1_tarski(A_81), C_82)=k1_xboole_0 | ~r2_hidden(A_81, C_82))), inference(resolution, [status(thm)], [c_415, c_4])).
% 2.13/1.31  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.31  tff(c_437, plain, (![C_82, A_81]: (k2_xboole_0(C_82, k1_tarski(A_81))=k2_xboole_0(C_82, k1_xboole_0) | ~r2_hidden(A_81, C_82))), inference(superposition, [status(thm), theory('equality')], [c_424, c_10])).
% 2.13/1.31  tff(c_454, plain, (![C_84, A_85]: (k2_xboole_0(C_84, k1_tarski(A_85))=C_84 | ~r2_hidden(A_85, C_84))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_437])).
% 2.13/1.31  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.31  tff(c_94, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.31  tff(c_134, plain, (![B_38, A_39]: (k3_tarski(k2_tarski(B_38, A_39))=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_12, c_94])).
% 2.13/1.31  tff(c_22, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.31  tff(c_140, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_134, c_22])).
% 2.13/1.31  tff(c_30, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.31  tff(c_160, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_30])).
% 2.13/1.31  tff(c_460, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_454, c_160])).
% 2.13/1.31  tff(c_498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_460])).
% 2.13/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  Inference rules
% 2.13/1.31  ----------------------
% 2.13/1.31  #Ref     : 0
% 2.13/1.31  #Sup     : 114
% 2.13/1.31  #Fact    : 0
% 2.13/1.31  #Define  : 0
% 2.13/1.31  #Split   : 0
% 2.13/1.31  #Chain   : 0
% 2.13/1.31  #Close   : 0
% 2.13/1.31  
% 2.13/1.31  Ordering : KBO
% 2.13/1.31  
% 2.13/1.31  Simplification rules
% 2.13/1.31  ----------------------
% 2.13/1.31  #Subsume      : 22
% 2.13/1.31  #Demod        : 18
% 2.13/1.31  #Tautology    : 65
% 2.13/1.31  #SimpNegUnit  : 0
% 2.13/1.31  #BackRed      : 1
% 2.13/1.31  
% 2.13/1.31  #Partial instantiations: 0
% 2.13/1.31  #Strategies tried      : 1
% 2.13/1.31  
% 2.13/1.31  Timing (in seconds)
% 2.13/1.31  ----------------------
% 2.13/1.31  Preprocessing        : 0.30
% 2.13/1.31  Parsing              : 0.17
% 2.13/1.31  CNF conversion       : 0.02
% 2.13/1.31  Main loop            : 0.21
% 2.13/1.31  Inferencing          : 0.09
% 2.13/1.31  Reduction            : 0.07
% 2.13/1.31  Demodulation         : 0.06
% 2.13/1.31  BG Simplification    : 0.01
% 2.13/1.31  Subsumption          : 0.03
% 2.13/1.31  Abstraction          : 0.01
% 2.13/1.31  MUC search           : 0.00
% 2.13/1.31  Cooper               : 0.00
% 2.13/1.31  Total                : 0.55
% 2.13/1.31  Index Insertion      : 0.00
% 2.13/1.31  Index Deletion       : 0.00
% 2.13/1.31  Index Matching       : 0.00
% 2.13/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
