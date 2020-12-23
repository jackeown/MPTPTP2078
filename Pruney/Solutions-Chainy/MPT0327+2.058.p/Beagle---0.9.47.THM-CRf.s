%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:38 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_30,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    ! [A_47,B_48] : k4_xboole_0(k2_xboole_0(A_47,B_48),B_48) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [B_48,A_47] : k5_xboole_0(B_48,k4_xboole_0(A_47,B_48)) = k2_xboole_0(B_48,k2_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_12])).

tff(c_235,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,k2_xboole_0(A_62,B_61)) = k2_xboole_0(B_61,A_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_260,plain,(
    ! [B_10,A_9] :
      ( k2_xboole_0(k4_xboole_0(B_10,A_9),B_10) = k2_xboole_0(k4_xboole_0(B_10,A_9),A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_235])).

tff(c_768,plain,(
    ! [B_87,A_88] :
      ( k2_xboole_0(k4_xboole_0(B_87,A_88),A_88) = B_87
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_260])).

tff(c_28,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_838,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_28])).

tff(c_850,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_838])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  
% 2.65/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.65/1.42  
% 2.65/1.42  %Foreground sorts:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Background operators:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Foreground operators:
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.65/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.42  
% 2.65/1.43  tff(f_60, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.65/1.43  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.65/1.43  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.65/1.43  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.65/1.43  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.65/1.43  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.65/1.43  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.65/1.43  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.43  tff(c_24, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.43  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.43  tff(c_56, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.43  tff(c_64, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.65/1.43  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.43  tff(c_12, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.43  tff(c_121, plain, (![A_47, B_48]: (k4_xboole_0(k2_xboole_0(A_47, B_48), B_48)=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.43  tff(c_127, plain, (![B_48, A_47]: (k5_xboole_0(B_48, k4_xboole_0(A_47, B_48))=k2_xboole_0(B_48, k2_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_12])).
% 2.65/1.43  tff(c_235, plain, (![B_61, A_62]: (k2_xboole_0(B_61, k2_xboole_0(A_62, B_61))=k2_xboole_0(B_61, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_127])).
% 2.65/1.43  tff(c_260, plain, (![B_10, A_9]: (k2_xboole_0(k4_xboole_0(B_10, A_9), B_10)=k2_xboole_0(k4_xboole_0(B_10, A_9), A_9) | ~r1_tarski(A_9, B_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_235])).
% 2.65/1.43  tff(c_768, plain, (![B_87, A_88]: (k2_xboole_0(k4_xboole_0(B_87, A_88), A_88)=B_87 | ~r1_tarski(A_88, B_87))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_260])).
% 2.65/1.43  tff(c_28, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.43  tff(c_838, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_768, c_28])).
% 2.65/1.43  tff(c_850, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_838])).
% 2.65/1.43  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_850])).
% 2.65/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.43  
% 2.65/1.43  Inference rules
% 2.65/1.43  ----------------------
% 2.65/1.43  #Ref     : 0
% 2.65/1.43  #Sup     : 216
% 2.65/1.43  #Fact    : 0
% 2.65/1.43  #Define  : 0
% 2.65/1.43  #Split   : 0
% 2.65/1.43  #Chain   : 0
% 2.65/1.43  #Close   : 0
% 2.65/1.43  
% 2.65/1.43  Ordering : KBO
% 2.65/1.43  
% 2.65/1.43  Simplification rules
% 2.65/1.43  ----------------------
% 2.65/1.43  #Subsume      : 2
% 2.65/1.43  #Demod        : 61
% 2.65/1.43  #Tautology    : 70
% 2.65/1.43  #SimpNegUnit  : 0
% 2.65/1.43  #BackRed      : 1
% 2.65/1.43  
% 2.65/1.43  #Partial instantiations: 0
% 2.65/1.43  #Strategies tried      : 1
% 2.65/1.43  
% 2.65/1.43  Timing (in seconds)
% 2.65/1.43  ----------------------
% 2.65/1.43  Preprocessing        : 0.31
% 2.65/1.43  Parsing              : 0.17
% 2.65/1.43  CNF conversion       : 0.02
% 2.65/1.43  Main loop            : 0.36
% 2.65/1.43  Inferencing          : 0.14
% 2.65/1.43  Reduction            : 0.12
% 2.65/1.43  Demodulation         : 0.09
% 2.65/1.43  BG Simplification    : 0.02
% 2.65/1.43  Subsumption          : 0.06
% 2.65/1.43  Abstraction          : 0.02
% 2.65/1.43  MUC search           : 0.00
% 2.65/1.43  Cooper               : 0.00
% 2.65/1.43  Total                : 0.69
% 2.65/1.43  Index Insertion      : 0.00
% 2.65/1.43  Index Deletion       : 0.00
% 2.65/1.43  Index Matching       : 0.00
% 2.65/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
